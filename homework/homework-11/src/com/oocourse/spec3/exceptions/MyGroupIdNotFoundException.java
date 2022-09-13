package com.oocourse.spec3.exceptions;

public class MyGroupIdNotFoundException extends GroupIdNotFoundException {

    private static Counter counter = new Counter();

    private static int id;

    public MyGroupIdNotFoundException(int id) {
        counter.addCount(id);
        MyGroupIdNotFoundException.id = id;
    }

    @Override
    public void print() {
        System.out.println(String.format("ginf-%d, %d-%d",
                counter.getTotalCount(), id, counter.getIdCount(id)));
    }

}
