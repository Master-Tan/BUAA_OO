package com.oocourse.spec3.exceptions;

public class MyMessageIdNotFoundException extends MessageIdNotFoundException {

    private static Counter counter = new Counter();

    private static int id;

    public MyMessageIdNotFoundException(int id) {
        counter.addCount(id);
        MyMessageIdNotFoundException.id = id;
    }

    @Override
    public void print() {
        System.out.println(String.format("minf-%d, %d-%d",
                counter.getTotalCount(), id, counter.getIdCount(id)));
    }

}
