package com.oocourse.spec2.exceptions;

public class MyEqualPersonIdException extends EqualPersonIdException {

    private static Counter counter = new Counter();

    private static int id;

    public MyEqualPersonIdException(int id) {
        counter.addCount(id);
        MyEqualPersonIdException.id = id;
    }

    @Override
    public void print() {
        System.out.println(String.format("epi-%d, %d-%d",
                counter.getTotalCount(), id, counter.getIdCount(id)));
    }
}
