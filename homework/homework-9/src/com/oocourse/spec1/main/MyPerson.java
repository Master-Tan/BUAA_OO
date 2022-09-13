package com.oocourse.spec1.main;

import java.util.ArrayList;

public class MyPerson implements Person {

    private int id;
    private String name;
    private int age;
    private ArrayList<Person> acquaintance = new ArrayList<>();
    private ArrayList<Integer> value = new ArrayList<>();

    public MyPerson(int id, String name, int age) {
        this.id = id;
        this.name = name;
        this.age = age;
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

    public void link(Person person, int value) {
        acquaintance.add(person);
        this.value.add(value);
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