package com.oocourse.spec3.exceptions;

public class MyEmojiIdNotFoundException extends EmojiIdNotFoundException {
    private static Counter counter = new Counter();

    private static int id;

    public MyEmojiIdNotFoundException(int id) {
        counter.addCount(id);
        MyEmojiIdNotFoundException.id = id;
    }

    @Override
    public void print() {
        System.out.println(String.format("einf-%d, %d-%d",
                counter.getTotalCount(), id, counter.getIdCount(id)));
    }

}
