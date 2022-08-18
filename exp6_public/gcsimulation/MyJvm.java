package gcsimulation;

import java.util.ArrayList;
import java.util.List;

public class MyJvm {
    private static final int DEFAULT_CAPACITY = 16;
    private static final int MAX_TENURING_THRESHOLD = 8;

    private final JvmHeap eden;
    private final ArrayList<JvmHeap> survive = new ArrayList<>();
    private int fromSurviveSpace = 1;
    private final JvmHeap tenured;

    MyJvm() {
        eden = new JvmHeap(DEFAULT_CAPACITY);
        survive.add(new JvmHeap(DEFAULT_CAPACITY));
        survive.add(new JvmHeap(DEFAULT_CAPACITY));
        tenured = new JvmHeap(DEFAULT_CAPACITY);
    }

    public void createObject(int count) {
        for (int i = 0; i < count; i++) {
            MyObject newObject = new MyObject();
            eden.add(newObject);

            if (eden.getSize() == DEFAULT_CAPACITY) {
                System.out.println("Eden reaches its capacity,triggered Minor Garbage Collection.");
                minorGC();
            }
        }
    }

    public void setUnreferenced(List<Integer> objectId) {
        eden.setUnreferencedId(objectId);
        survive.get(fromSurviveSpace).setUnreferencedId(objectId);
        tenured.setUnreferencedId(objectId);
    }

    public void removeUnreferenced() {
        eden.removeUnreferenced();
        survive.get(fromSurviveSpace).removeUnreferenced();
        tenured.removeUnreferenced();
    }

    public void minorGC() {
        for (int i = 1; i <= eden.getSize(); i++) {
            MyObject mo = (MyObject) eden.getElementData()[i];
            if (!mo.isReferenced()) {
                continue;
            }
            mo.setAge(mo.getAge() + 1);
            survive.get(1 - fromSurviveSpace).add(mo);
        }

        // TODO

        eden.setSize(0);
        survive.get(fromSurviveSpace).setSize(0);
        fromSurviveSpace = 1 - fromSurviveSpace;
    }

    public void majorGC() {
        Object[] oldElement = tenured.getElementData().clone();
        int oldSize = tenured.getSize();
        tenured.setSize(0);
        for (int i = 1; i <= oldSize; i++) {
            MyObject mo = (MyObject) oldElement[i];
            if (!mo.isReferenced()) {
                continue;
            }
            tenured.add(mo);
        }
    }

    public void getSnapShot() {
        System.out.println("Eden: " + eden.getSize());
        for (int i = 1; i <= eden.getSize(); i++) {
            MyObject mo = (MyObject) eden.getElementData()[i];
            System.out.print(mo.getId() + " ");
        }
        System.out.println("");

        System.out.println("Survive 0: " + survive.get(0).getSize());
        for (int i = 1; i <= survive.get(0).getSize(); i++) {
            MyObject mo = (MyObject) survive.get(0).getElementData()[i];
            System.out.print(mo.getId() + " ");
        }
        MyObject youngestInSurvive0 = survive.get(0).getYoungestOne();
        if (youngestInSurvive0 != null) {
            System.out.print(", the youngest one " + youngestInSurvive0.getId() +
                    "'s age is " + youngestInSurvive0.getAge());
        }
        System.out.println("");

        System.out.println("Survive 1: " + survive.get(1).getSize());
        for (int i = 1; i <= survive.get(1).getSize(); i++) {
            MyObject mo = (MyObject) survive.get(1).getElementData()[i];
            System.out.print(mo.getId() + " ");
        }
        MyObject youngestInSurvive1 = survive.get(1).getYoungestOne();
        if (youngestInSurvive1 != null) {
            System.out.print(", the youngest one " + youngestInSurvive1.getId() +
                    "'s age is " + youngestInSurvive1.getAge());
        }
        System.out.println("");

        System.out.println("Tenured: " + tenured.getSize());
        for (int i = 1; i <= tenured.getSize(); i++) {
            MyObject mo = (MyObject) tenured.getElementData()[i];
            System.out.print(mo.getId() + " ");
        }
        MyObject youngestInTenured = tenured.getYoungestOne();
        if (youngestInTenured != null) {
            System.out.print(", the youngest one " + youngestInTenured.getId() +
                    "'s age is " + youngestInTenured.getAge());
        }

        System.out.println("\n---------------------------------");
    }
}
