package com.oocourse.spec3.exceptions;

public class MyEqualEmojiIdException extends EqualEmojiIdException {
    private static Counter counter = new Counter();

    private static int id;

    public MyEqualEmojiIdException(int id) {
        counter.addCount(id);
        MyEqualEmojiIdException.id = id;
    }

    @Override
    public void print() {
        System.out.println(String.format("eei-%d, %d-%d",
                counter.getTotalCount(), id, counter.getIdCount(id)));
    }

}