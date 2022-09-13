package com.oocourse.spec3.exceptions;

public class MyEqualMessageIdException extends EqualMessageIdException {

    private static Counter counter = new Counter();

    private static int id;

    public MyEqualMessageIdException(int id) {
        counter.addCount(id);
        MyEqualMessageIdException.id = id;
    }

    @Override
    public void print() {
        System.out.println(String.format("emi-%d, %d-%d",
                counter.getTotalCount(), id, counter.getIdCount(id)));
    }
}
