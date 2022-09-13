package com.oocourse.spec3.main;

import com.oocourse.spec3.exceptions.EmojiIdNotFoundException;
import com.oocourse.spec3.exceptions.EqualEmojiIdException;
import com.oocourse.spec3.exceptions.EqualGroupIdException;
import com.oocourse.spec3.exceptions.EqualMessageIdException;
import com.oocourse.spec3.exceptions.EqualPersonIdException;
import com.oocourse.spec3.exceptions.EqualRelationException;
import com.oocourse.spec3.exceptions.GroupIdNotFoundException;
import com.oocourse.spec3.exceptions.MessageIdNotFoundException;
import com.oocourse.spec3.exceptions.MyEmojiIdNotFoundException;
import com.oocourse.spec3.exceptions.MyEqualEmojiIdException;
import com.oocourse.spec3.exceptions.MyEqualGroupIdException;
import com.oocourse.spec3.exceptions.MyEqualMessageIdException;
import com.oocourse.spec3.exceptions.MyEqualPersonIdException;
import com.oocourse.spec3.exceptions.MyEqualRelationException;
import com.oocourse.spec3.exceptions.MyGroupIdNotFoundException;
import com.oocourse.spec3.exceptions.MyMessageIdNotFoundException;
import com.oocourse.spec3.exceptions.MyPersonIdNotFoundException;
import com.oocourse.spec3.exceptions.MyRelationNotFoundException;
import com.oocourse.spec3.exceptions.PersonIdNotFoundException;
import com.oocourse.spec3.exceptions.RelationNotFoundException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

public class MyNetwork implements Network {

    private ArrayList<Person> people = new ArrayList<>();
    private ArrayList<Group> groups = new ArrayList<>();
    private ArrayList<Message> messages = new ArrayList<>();
    private ArrayList<Integer> emojiIdList = new ArrayList<>();
    private ArrayList<Integer> emojiHeatList = new ArrayList<>();

    private static HashMap<Person, Person> parent = new HashMap<>();

    private ArrayList<Person> beginLines = new ArrayList<>();
    private ArrayList<Person> endLines = new ArrayList<>();
    private ArrayList<Integer> values = new ArrayList<>();

    private HashMap<Person, Integer> totalPath = new HashMap<>();

    private HashMap<Person, HashSet<Person>> graph = new HashMap<>();

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
        HashSet<Person> hashSet = new HashSet<>();
        graph.put(person, hashSet);
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
            beginLines.add(getPerson(id1));
            endLines.add(getPerson(id2));
            values.add(value);
            HashSet<Person> hashSet;
            hashSet = graph.get(getPerson(id1));
            hashSet.add(getPerson(id2));
            hashSet = graph.get(getPerson(id2));
            hashSet.add(getPerson(id1));
            for (int i = 0; i < groups.size(); i++) {
                if (groups.get(i).hasPerson(getPerson(id1)) &&
                        groups.get(i).hasPerson(getPerson(id2))) {
                    ((MyGroup)groups.get(i)).setValueSum(groups.get(i).getValueSum() + 2 * value);
                }
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
    public int queryLeastConnection(int id) throws PersonIdNotFoundException {
        if (contains(id)) {
            int thisId = getRoot(getPerson(id)).getId();
            HashSet<Person> thisPeople = new HashSet<>();
            HashMap<Person, Person> thisParent = new HashMap<>();
            for (int i = 0; i < people.size(); i++) {
                if (getRoot(people.get(i)).getId() == thisId) {
                    thisPeople.add(people.get(i));
                    thisParent.put(people.get(i), null);
                }
            }
            ArrayList<Integer> min = new ArrayList<>();
            for (int i = 0; i < beginLines.size(); i++) {
                if (getRoot(beginLines.get(i)).getId() == thisId) {
                    min.add(i);
                }
            }
            min.sort((o1, o2) -> Integer.compare(values.get(o1) - values.get(o2), 0));
            ArrayList<Person> subgroup = new ArrayList<>();
            int next;
            while (subgroup.size() < (thisPeople.size() - 1) * 2) {
                next = min.get(0);
                min.remove(0);
                Person beginRoot = beginLines.get(next);
                while (thisParent.get(beginRoot) != null) {
                    beginRoot = thisParent.get(beginRoot);
                }
                if (!beginRoot.equals(beginLines.get(next))) {
                    thisParent.put(beginLines.get(next), beginRoot);
                }
                Person endRoot = endLines.get(next);
                while (thisParent.get(endRoot) != null) {
                    endRoot = thisParent.get(endRoot);
                }
                if (!endRoot.equals(endLines.get(next))) {
                    thisParent.put(endLines.get(next), endRoot);
                }
                if (beginRoot != endRoot) {
                    subgroup.add(beginLines.get(next));
                    subgroup.add(endLines.get(next));
                    thisParent.put(beginRoot, endRoot);
                }
            }
            int sum = 0;
            for (int i = 0; i < (subgroup.size() / 2); i++) {
                sum += subgroup.get(2 * i).queryValue(subgroup.get(2 * i + 1));
            }
            return sum;
        } else {
            throw new MyPersonIdNotFoundException(id);
        }
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
    public int queryGroupPeopleSum(int id) throws GroupIdNotFoundException {
        for (int i = 0; i < groups.size(); i++) {
            if (groups.get(i).getId() == id) {
                return (groups.get(i).getSize());
            }
        }
        throw new MyGroupIdNotFoundException(id);
    }

    @Override
    public int queryGroupValueSum(int id) throws GroupIdNotFoundException {
        for (int i = 0; i < groups.size(); i++) {
            if (groups.get(i).getId() == id) {
                return (groups.get(i).getValueSum());
            }
        }
        throw new MyGroupIdNotFoundException(id);
    }

    @Override
    public int queryGroupAgeVar(int id) throws GroupIdNotFoundException {
        for (int i = 0; i < groups.size(); i++) {
            if (groups.get(i).getId() == id) {
                return (groups.get(i).getAgeVar());
            }
        }
        throw new MyGroupIdNotFoundException(id);
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

    @Override
    public boolean containsMessage(int id) {
        for (int i = 0; i < messages.size(); i++) {
            if (messages.get(i).getId() == id) {
                return true;
            }
        }
        return false;
    }

    @Override
    public void addMessage(Message message) throws EqualMessageIdException,
            EmojiIdNotFoundException, EqualPersonIdException {
        for (int i = 0; i < messages.size(); i++) {
            if (messages.get(i).equals(message)) {
                throw new MyEqualMessageIdException(message.getId());
            }
        }
        if (message instanceof EmojiMessage &&
                !containsEmojiId(((EmojiMessage) message).getEmojiId())) {
            throw new MyEmojiIdNotFoundException(((EmojiMessage) message).getEmojiId());
        }
        if (message.getType() == 0 && message.getPerson1().equals(message.getPerson2())) {
            throw new MyEqualPersonIdException(message.getPerson1().getId());
        }
        messages.add(message);
    }

    @Override
    public Message getMessage(int id) {
        if (containsMessage(id)) {
            for (int i = 0; i < messages.size(); i++) {
                if (messages.get(i).getId() == id) {
                    return messages.get(i);
                }
            }
        }
        return null;
    }

    @Override
    public void sendMessage(int id) throws RelationNotFoundException,
            MessageIdNotFoundException, PersonIdNotFoundException {
        if (!containsMessage(id)) {
            throw new MyMessageIdNotFoundException(id);
        }
        if (getMessage(id).getType() == 0 &&
                !(getMessage(id).getPerson1().isLinked(getMessage(id).getPerson2()))) {
            throw new MyRelationNotFoundException(getMessage(id).getPerson1().getId(),
                    getMessage(id).getPerson2().getId());
        }
        if (getMessage(id).getType() == 1 &&
                !(getMessage(id).getGroup().hasPerson(getMessage(id).getPerson1()))) {
            throw new MyPersonIdNotFoundException(getMessage(id).getPerson1().getId());
        }
        Message message = getMessage(id);
        Person person1;
        person1 = message.getPerson1();
        Person person2;
        person2 = message.getPerson2();
        if (message.getType() == 0) {
            person1.addSocialValue(message.getSocialValue());
            person2.addSocialValue(message.getSocialValue());
            ((MyPerson) person2).addMessage(0, getMessage(id));
            if (message instanceof RedEnvelopeMessage) {
                person1.addMoney(
                        -1 * (((RedEnvelopeMessage) getMessage(id)).getMoney()));
                person2.addMoney(
                        ((RedEnvelopeMessage)getMessage(id)).getMoney());
            }
        } else if (message.getType() == 1) {
            ((MyGroup) message.getGroup()).addSocialValue(message.getSocialValue());
            if (message instanceof RedEnvelopeMessage) {
                int addMoney;
                addMoney = (((RedEnvelopeMessage) message).getMoney()) /
                        message.getGroup().getSize();
                person1.addMoney(
                        -1 * addMoney * (message.getGroup().getSize() - 1));
                for (int i = 0; i < people.size(); i++) {
                    if (message.getGroup().hasPerson(people.get(i))) {
                        if (!people.get(i).equals(person1)) {
                            people.get(i).addMoney(addMoney);
                        }
                    }
                }
            }
        }
        if (message instanceof EmojiMessage) {
            for (int i = 0; i < emojiIdList.size(); i++) {
                if (((EmojiMessage) message).getEmojiId() == emojiIdList.get(i)) {
                    emojiHeatList.set(i, emojiHeatList.get(i) + 1);
                }
            }
        }
        messages.remove(getMessage(id));
    }

    @Override
    public int querySocialValue(int id) throws PersonIdNotFoundException {
        if (contains(id)) {
            return (getPerson(id).getSocialValue());
        }
        throw new MyPersonIdNotFoundException(id);
    }

    @Override
    public List<Message> queryReceivedMessages(int id) throws PersonIdNotFoundException {
        if (contains(id)) {
            return (getPerson(id).getReceivedMessages());
        }
        throw new MyPersonIdNotFoundException(id);
    }

    @Override
    public boolean containsEmojiId(int id) {
        for (int i = 0; i < emojiIdList.size(); i++) {
            if (emojiIdList.get(i) == id) {
                return true;
            }
        }
        return false;
    }

    @Override
    public void storeEmojiId(int id) throws EqualEmojiIdException {
        for (int i = 0; i < emojiIdList.size(); i++) {
            if (emojiIdList.get(i) == id) {
                throw new MyEqualEmojiIdException(id);
            }
        }
        emojiIdList.add(id);
        emojiHeatList.add(0);
    }

    @Override
    public int queryMoney(int id) throws PersonIdNotFoundException {
        if (!contains(id)) {
            throw new MyPersonIdNotFoundException(id);
        }
        return getPerson(id).getMoney();
    }

    @Override
    public int queryPopularity(int id) throws EmojiIdNotFoundException {
        for (int i = 0; i < emojiIdList.size(); i++) {
            if (emojiIdList.get(i) == id) {
                return emojiHeatList.get(i);
            }
        }
        throw new MyEmojiIdNotFoundException(id);
    }

    @Override
    public int deleteColdEmoji(int limit) {
        return MyNetWork2.deleteColdEmoji(this, emojiIdList, emojiHeatList, messages, limit);
    }

    @Override
    public void clearNotices(int personId) throws PersonIdNotFoundException {
        if (!contains(personId)) {
            throw new MyPersonIdNotFoundException(personId);
        }
        ((MyPerson)getPerson(personId)).clearNotices();
    }

    @Override
    public int sendIndirectMessage(int id) throws MessageIdNotFoundException {
        totalPath.clear();
        return MyNetWork2.sendIndirectMessage(this, people, totalPath,
                emojiIdList, emojiHeatList, messages, graph, id);
    }

    public Person getRoot(Person person) {
        Person root = person;
        while (parent.get(root) != null) {
            root = parent.get(root);
        }
        if (!root.equals(person)) {
            parent.put(person, root);
        }
        return root;
    }

}
