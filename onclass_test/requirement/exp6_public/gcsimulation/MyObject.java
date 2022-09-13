package gcsimulation;

import java.util.Objects;

public class MyObject implements Comparable<MyObject> {
    private static int totalId = 0;
    private final /*@ spec_public @*/ int id;
    private /*@ spec_public @*/ boolean referenced;
    private /*@ spec_public @*/ int age;

    MyObject() {
        id = totalId;
        totalId++;
        referenced = true;
        age = 0;
    }

    /*@ public normal_behavior
      @ assignable age;
      @ ensures age == newAge;
      @*/
    public void setAge(int newAge) {
        this.age = newAge;
    }

    //@ ensures \result == age;
    public /*@ pure @*/ int getAge() {
        return age;
    }

    //@ ensures \result == id;
    public /*@ pure @*/ int getId() {
        return id;
    }

    /*@ public normal_behavior
      @ assignable referenced;
      @ ensures referenced;
      @*/
    public void setReferenced() {
        this.referenced = true;
    }

    /*@ public normal_behavior
      @ assignable referenced;
      @ ensures !referenced;
      @*/
    public void setUnreferenced() {
        this.referenced = false;
    }

    //@ ensures \result == referenced;
    public /*@ pure @*/ boolean isReferenced() {
        return referenced;
    }

    /*@ also
      @ public normal_behavior
      @ requires this == o;
      @ ensures \result == true;
      @ also
      @ requires this != o && !(o instanceof MyObject);
      @ ensures \result == false;
      @ also
      @ requires this != o && o instanceof MyObject;
      @ ensures \result == (id == ((MyObject) o).getId() &&
      @         referenced == ((MyObject) o).isReferenced() &&
      @         age == ((MyObject) o).getAge());
      @*/
    @Override
    public /*@ pure @*/ boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof MyObject)) {
            return false;
        }
        MyObject myObject = (MyObject) o;
        return id == myObject.getId() && referenced == myObject.isReferenced()
                && age == myObject.getAge();
    }

    @Override
    public int hashCode() {
        return Objects.hash(id, referenced, age);
    }

    /*@ also
      @ public normal_behavior
      @ requires object != null;
      @ ensures ((age < object.age) || (age == object.age && id < object.id)) ==> (\result == -1);
      @ ensures ((age > object.age) || (age == object.age && id > object.id)) ==> (\result == 1);
      @ ensures ((age == object.age) && (id == object.id)) ==> (\result == 0);
      @ also
      @ public exceptional_behavior
      @ signals (NullPointerException e) object == null;
      @*/
    @Override
    public /*@ pure @*/ int compareTo(MyObject object) {
        // TODO
    }
}
