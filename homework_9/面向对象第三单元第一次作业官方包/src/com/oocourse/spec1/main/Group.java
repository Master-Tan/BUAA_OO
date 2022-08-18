package com.oocourse.spec1.main;

public interface Group {

    /*@ public instance model int id;
      @ public instance model non_null Person[] people;
      @*/

    //@ ensures \result == id;
    public /*@ pure @*/ int getId();

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Group;
      @ assignable \nothing;
      @ ensures \result == (((Group) obj).getId() == id);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Group);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public /*@ pure @*/ boolean equals(Object obj);

    /*@ public normal_behavior
      @ requires !hasPerson(person);
      @ assignable people;
      @ ensures (\forall Person p; \old(hasPerson(p)); hasPerson(p));
      @ ensures \old(people.length) == people.length - 1;
      @ ensures hasPerson(person);
      @*/
    public void addPerson(/*@ non_null @*/Person person);

    //@ ensures \result == (\exists int i; 0 <= i && i < people.length; people[i].equals(person));
    public /*@ pure @*/ boolean hasPerson(Person person);

    /*@ ensures \result == (\sum int i; 0 <= i && i < people.length; 
      @          (\sum int j; 0 <= j && j < people.length && 
      @           people[i].isLinked(people[j]); people[i].queryValue(people[j])));
      @*/
    public /*@ pure @*/ int getValueSum();

    /*@ ensures \result == (people.length == 0? 0:
      @          ((\sum int i; 0 <= i && i < people.length; people[i].getAge()) / people.length));
      @*/
    public /*@ pure @*/ int getAgeMean();

    /*@ ensures \result == (people.length == 0? 0 : ((\sum int i; 0 <= i && i < people.length; 
      @          (people[i].getAge() - getAgeMean()) * (people[i].getAge() - getAgeMean())) / 
      @           people.length));
      @*/
    public /*@ pure @*/ int getAgeVar();

    /*@ public normal_behavior
      @ requires hasPerson(person) == true;
      @ assignable people;
      @ ensures (\forall Person p; hasPerson(p); \old(hasPerson(p)));
      @ ensures \old(people.length) == people.length + 1;
      @ ensures hasPerson(person) == false;
      @*/
    public void delPerson(/*@ non_null @*/Person person);

    //@ ensures \result == people.length;
    public /*@ pure @*/ int getSize();
}