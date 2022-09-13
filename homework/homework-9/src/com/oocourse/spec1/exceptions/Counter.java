package com.oocourse.spec1.exceptions;

import java.util.HashMap;

public class Counter {

    private HashMap<Integer, Integer> counter;
    private int totalCounter;

    public Counter() {
        counter = new HashMap();
        totalCounter = 0;
    }

    public void addCount(int id) {
        if (counter.containsKey(id)) {
            counter.put(id, counter.get(id) + 1);
        } else {
            counter.put(id, 1);
        }
        totalCounter++;
    }

    public void addDoubleCount(int id1, int id2) {
        addCount(id1);
        addCount(id2);
        totalCounter--;
    }

    public int getTotalCount() {
        return totalCounter;
    }

    public int getIdCount(int id) {
        return counter.get(id);
    }

}
