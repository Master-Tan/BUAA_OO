package com.oocourse.spec1.main;

import java.util.ArrayList;

public class MyGroup implements Group {

    private int id;
    private ArrayList<Person> people = new ArrayList<>();

    public MyGroup(int id) {
        this.id = id;
    }

    @Override
    public int getId() {
        return id;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof Group) {
            return (((Group) obj).getId() == id);
        }
        if (obj == null || !(obj instanceof Group)) {
            return false;
        }
        return true;
    }

    @Override
    public void addPerson(Person person) {
        if (!hasPerson(person)) {
            people.add(person);
        }
    }

    @Override
    public boolean hasPerson(Person person) {
        for (int i = 0; i < people.size(); i++) {
            if (people.get(i).equals(person)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public int getValueSum() {
        int sum;
        sum = 0;
        for (int i = 0; i < people.size(); i++) {
            for (int j = 0; j < people.size(); j++) {
                if (people.get(i).isLinked(people.get(j))) {
                    sum += people.get(i).queryValue((people.get(j)));
                }
            }
        }
        return sum;
    }

    @Override
    public int getAgeMean() {
        if (people.size() == 0) {
            return 0;
        }
        int sum;
        sum = 0;
        for (int i = 0; i < people.size(); i++) {
            sum += people.get(i).getAge();
        }
        return sum / people.size();
    }

    @Override
    public int getAgeVar() {
        if (people.size() == 0) {
            return 0;
        }
        int sum;
        sum = 0;
        for (int i = 0; i < people.size(); i++) {
            sum += (people.get(i).getAge() - getAgeMean()) *
                    (people.get(i).getAge() - getAgeMean());
        }
        return sum / people.size();
    }

    @Override
    public void delPerson(Person person) {
        if (hasPerson(person)) {
            people.remove(person);
        }
    }

    @Override
    public int getSize() {
        return people.size();
    }
}
