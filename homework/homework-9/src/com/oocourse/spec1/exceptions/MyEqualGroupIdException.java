package com.oocourse.spec1.exceptions;

public class MyEqualGroupIdException extends EqualGroupIdException {

    private static Counter counter = new Counter();

    private static int id;

    public MyEqualGroupIdException(int id) {
        counter.addCount(id);
        MyEqualGroupIdException.id = id;
    }

    @Override
    public void print() {
        System.out.println(String.format("egi-%d, %d-%d",
                counter.getTotalCount(), id, counter.getIdCount(id)));
    }

}
