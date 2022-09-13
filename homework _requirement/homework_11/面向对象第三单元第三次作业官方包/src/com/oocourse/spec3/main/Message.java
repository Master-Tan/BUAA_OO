package com.oocourse.spec3.main;

public interface Message {
    /*@ public instance model int id;
      @ public instance model int socialValue;
      @ public instance model int type;
      @ public instance model non_null Person person1;
      @ public instance model nullable Person person2;
      @ public instance model nullable Group group;
      @*/

    //@ ensures \result == type;
    public /*@ pure @*/ int getType();

    //@ ensures \result == id;
    public /*@ pure @*/ int getId();

    //@ ensures \result == socialValue;
    public /*@ pure @*/ int getSocialValue();

    //@ ensures \result == person1;
    public /*@ pure @*/ Person getPerson1();

    /*@ requires person2 != null;
      @ ensures \result == person2;
      @*/
    public /*@ pure @*/ Person getPerson2();

    /*@ requires group != null;
      @ ensures \result == group;
      @*/
    public /*@ pure @*/ Group getGroup();

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Message;
      @ assignable \nothing;
      @ ensures \result == (((Message) obj).getId() == id);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Message);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public /*@ pure @*/ boolean equals(Object obj);
}
