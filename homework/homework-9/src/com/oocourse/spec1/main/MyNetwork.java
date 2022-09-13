package com.oocourse.spec1.main;

import com.oocourse.spec1.exceptions.EqualGroupIdException;
import com.oocourse.spec1.exceptions.EqualPersonIdException;
import com.oocourse.spec1.exceptions.EqualRelationException;
import com.oocourse.spec1.exceptions.GroupIdNotFoundException;
import com.oocourse.spec1.exceptions.MyEqualGroupIdException;
import com.oocourse.spec1.exceptions.MyEqualPersonIdException;
import com.oocourse.spec1.exceptions.MyEqualRelationException;
import com.oocourse.spec1.exceptions.MyGroupIdNotFoundException;
import com.oocourse.spec1.exceptions.MyPersonIdNotFoundException;
import com.oocourse.spec1.exceptions.MyRelationNotFoundException;
import com.oocourse.spec1.exceptions.PersonIdNotFoundException;
import com.oocourse.spec1.exceptions.RelationNotFoundException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class MyNetwork implements Network {

    private static HashMap<Person, Person> parent = new HashMap<>();

    private ArrayList<Person> people = new ArrayList<>();
    private ArrayList<Group> groups = new ArrayList<>();

    public MyNetwork() {
    }

    @Override
    public boolean contains(int id) {
        for (int i = 0; i < people.size(); i++) {
            if (people.get(i).getId() == id) {
                return true;
            }
        }
        return false;
    }

    @Override
    public Person getPerson(int id) {
        if (contains(id)) {
            for (int i = 0; i < people.size(); i++) {
                if (people.get(i).getId() == id) {
                    return people.get(i);
                }
            }
        }
        return null;
    }

    @Override
    public void addPerson(Person person) throws EqualPersonIdException {
        for (int i = 0; i < people.size(); i++) {
            if (people.get(i).equals(person)) {
                throw new MyEqualPersonIdException(person.getId());
            }
        }
        people.add(person);
        parent.put(person, null);
    }

    @Override
    public void addRelation(int id1, int id2, int value)
            throws PersonIdNotFoundException, EqualRelationException {
        if (contains(id1) && contains(id2) && !getPerson(id1).isLinked(getPerson(id2))) {
            ((MyPerson) getPerson(id1)).link(getPerson(id2), value);
            ((MyPerson) getPerson(id2)).link(getPerson(id1), value);
            if (!getRoot(getPerson(id1)).equals(getRoot(getPerson(id2)))) {
                parent.put(getRoot(getPerson(id1)), getRoot(getPerson(id2)));
                // System.out.println(id1 + " kk " + getRoot(getPerson(id2)).getId());
            }
        } else {
            if (!contains(id1)) {
                throw new MyPersonIdNotFoundException(id1);
            } else if (contains(id1) && !contains(id2)) {
                throw new MyPersonIdNotFoundException(id2);
            } else {
                throw new MyEqualRelationException(id1, id2);
            }
        }
    }

    @Override
    public int queryValue(int id1, int id2)
            throws PersonIdNotFoundException, RelationNotFoundException {
        if (contains(id1) && contains(id2) && getPerson(id1).isLinked(getPerson(id2))) {
            return getPerson(id1).queryValue(getPerson(id2));
        } else {
            if (!contains(id1)) {
                throw new MyPersonIdNotFoundException(id1);
            } else if (contains(id1) && !contains(id2)) {
                throw new MyPersonIdNotFoundException(id2);
            } else {
                throw new MyRelationNotFoundException(id1, id2);
            }
        }
    }

    @Override
    public int queryPeopleSum() {
        return people.size();
    }

    @Override
    public boolean isCircle(int id1, int id2)
            throws PersonIdNotFoundException {
        if (contains(id1) && contains(id2)) {
            return (getRoot(getPerson(id1)).equals(getRoot(getPerson(id2))));
            //            ArrayList<Integer> persons = new ArrayList<>();
            //            persons.add(id1);
            //            return ((MyPerson)getPerson(id1)).findCircle(id2, persons);
        } else {
            if (!contains(id1)) {
                throw new MyPersonIdNotFoundException(id1);
            } else {
                throw new MyPersonIdNotFoundException(id2);
            }
        }
    }

    @Override
    public int queryBlockSum() {
        HashSet<Person> sum = new HashSet<>();
        for (int i = 0; i < people.size(); i++) {
            sum.add(getRoot(people.get(i)));
        }
        return sum.size();
    }

    @Override
    public void addGroup(Group group) throws EqualGroupIdException {
        for (int i = 0; i < groups.size(); i++) {
            if (groups.get(i).equals(group)) {
                throw new MyEqualGroupIdException(group.getId());
            }
        }
        groups.add(group);
    }

    @Override
    public Group getGroup(int id) {
        for (int i = 0; i < groups.size(); i++) {
            if (groups.get(i).getId() == id) {
                return groups.get(i);
            }
        }
        return null;
    }

    @Override
    public void addToGroup(int id1, int id2)
            throws GroupIdNotFoundException, PersonIdNotFoundException, EqualPersonIdException {
        for (int i = 0; i < groups.size(); i++) {
            if (groups.get(i).getId() == id2) {
                for (int j = 0; j < people.size(); j++) {
                    if (people.get(j).getId() == id1) {
                        if (getGroup(id2).hasPerson(getPerson(id1)) == false) {
                            if (getGroup(id2).getSize() < 1111) {
                                getGroup(id2).addPerson(getPerson(id1));
                            }
                            return;
                        }
                        throw new MyEqualPersonIdException(id1);
                    }
                }
                throw new MyPersonIdNotFoundException(id1);
            }
        }
        throw new MyGroupIdNotFoundException(id2);
    }

    @Override
    public void delFromGroup(int id1, int id2)
            throws GroupIdNotFoundException, PersonIdNotFoundException, EqualPersonIdException {
        for (int i = 0; i < groups.size(); i++) {
            if (groups.get(i).getId() == id2) {
                for (int j = 0; j < people.size(); j++) {
                    if (people.get(j).getId() == id1) {
                        if (getGroup(id2).hasPerson(getPerson(id1)) == true) {
                            getGroup(id2).delPerson(getPerson(id1));
                            return;
                        }
                        throw new MyEqualPersonIdException(id1);
                    }
                }
                throw new MyPersonIdNotFoundException(id1);
            }
        }
        throw new MyGroupIdNotFoundException(id2);
    }

    public Person getRoot(Person person) {
        Person root = person;
        while (parent.get(root) != null) {
            root = parent.get(root);
        }
        return root;
    }

}
