package com.oocourse.spec3.main;

import java.util.List;

public interface Person extends Comparable<Person> {

    /*@ public instance model int id;
      @ public instance model non_null String name;
      @ public instance model int age;
      @ public instance model non_null Person[] acquaintance;
      @ public instance model non_null int[] value;
      @ public instance model int money;
      @ public instance model int socialValue;
      @ public instance model non_null Message[] messages;
      @*/

    //@ ensures \result == id;
    /*@ pure @*/ int getId();

    //@ ensures \result.equals(name);
    /*@ pure @*/ String getName();

    //@ ensures \result == age;
    /*@ pure @*/ int getAge();

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Person;
      @ assignable \nothing;
      @ ensures \result == (((Person) obj).getId() == id);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Person);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    /*@ pure @*/ boolean equals(Object obj);

    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == (\exists int i; 0 <= i && i < acquaintance.length; 
      @                     acquaintance[i].getId() == person.getId()) || person.getId() == id;
      @*/
    /*@ pure @*/ boolean isLinked(Person person);

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < acquaintance.length; 
      @          acquaintance[i].getId() == person.getId());
      @ assignable \nothing;
      @ ensures (\exists int i; 0 <= i && i < acquaintance.length; 
      @         acquaintance[i].getId() == person.getId() && \result == value[i]);
      @ also
      @ public normal_behavior
      @ requires (\forall int i; 0 <= i && i < acquaintance.length; 
      @          acquaintance[i].getId() != person.getId());
      @ ensures \result == 0;
      @*/
    /*@ pure @*/ int queryValue(Person person);

    //@ also ensures \result == name.compareTo(p2.getName());
    /*@ pure @*/ int compareTo(Person p2);

    /*@ public normal_behavior
      @ assignable socialValue;
      @ ensures socialValue == \old(socialValue) + num;
      @*/
    void addSocialValue(int num);

    //@ ensures \result == socialValue;
    /*@ pure @*/ int getSocialValue();

    /*@ ensures (\result.size() == messages.length) && 
      @           (\forall int i; 0 <= i && i < messages.length; 
      @             messages[i] == \result.get(i));
      @*/
    /*@ pure @*/ List<Message> getMessages();

    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures (\forall int i; 0 <= i && i < messages.length && i <= 3;
      @           \result.contains(messages[i]) && \result.get(i) == messages[i]);
      @ ensures \result.size() == ((messages.length < 4)? messages.length: 4);
     */
    /*@ pure @*/ List<Message> getReceivedMessages();

    /*@ public normal_behavior
      @ assignable money;
      @ ensures money == \old(money) + num;
      @*/
    void addMoney(int num);

    //@ ensures \result == money;
    /*@ pure @*/ int getMoney();

}
