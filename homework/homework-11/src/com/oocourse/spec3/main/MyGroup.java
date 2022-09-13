package com.oocourse.spec3.main;

import java.util.ArrayList;

public class MyGroup implements Group {

    private int id;

    private int valueSum;

    private int sumAge;

    private ArrayList<Person> people = new ArrayList<>();

    public MyGroup(int id) {
        this.id = id;
        this.valueSum = 0;
        this.sumAge = 0;
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
            for (int i = 0; i < people.size(); i++) {
                valueSum += (people.get(i).queryValue(person) * 2);
            }
            sumAge += person.getAge();
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
        return valueSum;
    }

    @Override
    public int getAgeMean() {
        if (people.size() == 0) {
            return 0;
        }
        return sumAge / people.size();
    }

    @Override
    public int getAgeVar() {
        if (people.size() == 0) {
            return 0;
        }
        int sum;
        int tmp;
        sum = 0;
        int ageMean;
        ageMean = getAgeMean();
        for (int i = 0; i < people.size(); i++) {
            tmp = (people.get(i).getAge() - ageMean);
            sum += tmp * tmp;
        }
        return sum / people.size();
    }

    @Override
    public void delPerson(Person person) {
        if (hasPerson(person)) {
            for (int i = 0; i < people.size(); i++) {
                valueSum -= (person.queryValue(people.get(i)) * 2);
            }
            sumAge -= person.getAge();
            people.remove(person);
        }
    }

    @Override
    public int getSize() {
        return people.size();
    }

    public void addSocialValue(int num) {
        for (int i = 0; i < people.size(); i++) {
            people.get(i).addSocialValue(num);
        }
    }

    public void setValueSum(int valueSum) {
        this.valueSum = valueSum;
    }
}
