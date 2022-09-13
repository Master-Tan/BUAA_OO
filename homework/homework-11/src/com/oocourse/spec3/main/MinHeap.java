package com.oocourse.spec3.main;

import java.util.ArrayList;

public class MinHeap {

    private ArrayList<Integer> minHeapDist;
    private ArrayList<Person> minHeapPerson;
    private int cnt;

    public MinHeap() {
        this.minHeapDist = new ArrayList<>();
        minHeapDist.add(null);
        this.minHeapPerson = new ArrayList<>();
        minHeapPerson.add(null);
        cnt = 0;
    }

    public void add(Person person, int queryValue) {
        minHeapPerson.add(person);
        minHeapDist.add(queryValue);
        cnt++;
        int i;
        i = cnt;
        while (i > 1) {
            if (queryValue < minHeapDist.get(i / 2)) {
                minHeapDist.set(i, minHeapDist.get(i / 2));
                minHeapPerson.set(i, minHeapPerson.get(i / 2));
            } else {
                break;
            }
            i = i / 2;
        }
        minHeapDist.set(i, queryValue);
        minHeapPerson.set(i, person);
    }

    public Person get() {
        Person outPerson;
        outPerson = minHeapPerson.get(1);
        int value;
        value = minHeapDist.get(cnt);
        Person person;
        person = minHeapPerson.get(cnt);
        cnt--;
        int i = 1;
        while (i * 2 <= cnt) {
            int min;
            if (i * 2 == cnt) {
                min = 2 * i;
                if (value > minHeapDist.get(min)) {
                    minHeapDist.set(i, minHeapDist.get(min));
                    minHeapPerson.set(i, minHeapPerson.get(min));
                } else {
                    break;
                }
            } else {
                if (minHeapDist.get(2 * i) <= minHeapDist.get(2 * i + 1)) {
                    min = 2 * i;
                } else {
                    min = 2 * i + 1;
                }
                if (value > minHeapDist.get(min)) {
                    minHeapDist.set(i, minHeapDist.get(min));
                    minHeapPerson.set(i, minHeapPerson.get(min));
                } else {
                    break;
                }
            }
            i = min;
        }
        minHeapDist.set(i, value);
        minHeapPerson.set(i, person);
        return outPerson;
    }

    public int getDist() {
        return minHeapDist.get(1);
    }

    //    public void changeDist(Person inPerson, int queryValue) {
    //        int i;
    //        for (i = 1; i < minHeapPerson.size(); i++) {
    //            if (minHeapPerson.get(i).equals(inPerson)) {
    //                break;
    //            }
    //        }
    //        int value;
    //        if (queryValue > minHeapDist.get(i)) {
    //            value = minHeapDist.get(i);
    //        } else {
    //            value = queryValue;
    //        }
    //        Person person = minHeapPerson.get(i);
    //        while (i > 1) {
    //            if (queryValue < minHeapDist.get(i / 2)) {
    //                minHeapDist.set(i, minHeapDist.get(i / 2));
    //                minHeapPerson.set(i, minHeapPerson.get(i / 2));
    //            } else {
    //                break;
    //            }
    //            i = i / 2;
    //        }
    //        minHeapDist.set(i, value);
    //        minHeapPerson.set(i, person);
    //    }
}
