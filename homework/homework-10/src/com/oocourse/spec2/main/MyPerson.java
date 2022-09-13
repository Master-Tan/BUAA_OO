package com.oocourse.spec2.main;

import java.util.ArrayList;
import java.util.List;

public class MyPerson implements Person {

    private int id;
    private String name;
    private int age;
    private ArrayList<Person> acquaintance = new ArrayList<>();
    private ArrayList<Integer> value = new ArrayList<>();
    private int money;
    private int socialValue;
    private ArrayList<Message> messages = new ArrayList<>();

    public MyPerson(int id, String name, int age) {
        this.id = id;
        this.name = name;
        this.age = age;
        this.money = 0;
        this.socialValue = 0;
    }

    @Override
    public int getId() {
        return id;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public int getAge() {
        return age;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof Person) {
            return (((Person) obj).getId() == id);
        } else {
            return false;
        }
    }

    @Override
    public boolean isLinked(Person person) {
        if (person.getId() == id) {
            return true;
        }
        for (int i = 0; i < acquaintance.size(); i++) {
            if (acquaintance.get(i).getId() == person.getId()) {
                return true;
            }
        }
        return false;
    }

    @Override
    public int queryValue(Person person) {
        for (int i = 0; i < acquaintance.size(); i++) {
            if (acquaintance.get(i).getId() == person.getId()) {
                return value.get(i);
            }
        }
        return 0;
    }

    @Override
    public int compareTo(Person p2) {
        return (name.compareTo(p2.getName()));
    }

    @Override
    public void addSocialValue(int num) {
        socialValue += num;
    }

    @Override
    public int getSocialValue() {
        return socialValue;
    }

    @Override
    public List<Message> getMessages() {
        ArrayList<Message> newMessages = new ArrayList<>();
        for (int i = 0; i < messages.size(); i++) {
            newMessages.add(messages.get(i));
        }
        return newMessages;
    }

    @Override
    public List<Message> getReceivedMessages() {
        ArrayList<Message> newMessages = new ArrayList<>();
        for (int i = 0; i < messages.size() && i <= 3; i++) {
            newMessages.add(messages.get(i));
        }
        return newMessages;
    }

    @Override
    public void addMoney(int num) {
        money = money + num;
    }

    @Override
    public int getMoney() {
        return money;
    }

    public void link(Person person, int value) {
        acquaintance.add(person);
        this.value.add(value);
    }

    public void addMessage(int index, Message message) {
        if (messages.size() == index) {
            messages.add(message);
        } else {
            messages.add(index, message);
        }
    }

    //    boolean findCircle(int id2, ArrayList<Integer> persons) {
    //        boolean flag = false;
    //        for (int i = 0; i < acquaintance.size(); i++) {
    //            if (acquaintance.get(i).getId() == id2) {
    //                flag = true;
    //            } else {
    //                if (!persons.contains(acquaintance.get(i).getId())) {
    //                    persons.add(acquaintance.get(i).getId());
    //                    if (((MyPerson)acquaintance.get(i)).findCircle(id2, persons)) {
    //                        flag = true;
    //                    }
    //                    persons.remove((Integer)acquaintance.get(i).getId());
    //                }
    //            }
    //        }
    //        return flag;
    //    }
}