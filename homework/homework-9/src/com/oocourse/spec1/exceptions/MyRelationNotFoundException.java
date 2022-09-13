package com.oocourse.spec1.exceptions;

public class MyRelationNotFoundException extends RelationNotFoundException {

    private static Counter counter = new Counter();

    private static int id1;

    private static int id2;

    public MyRelationNotFoundException(int id1, int id2) {
        if (id1 != id2) {
            counter.addDoubleCount(id1, id2);
        } else {
            counter.addCount(id1);
        }
        MyRelationNotFoundException.id1 = id1;
        MyRelationNotFoundException.id2 = id2;
    }

    @Override
    public void print() {
        if (id1 < id2) {
            System.out.println(String.format("rnf-%d, %d-%d, %d-%d",
                    counter.getTotalCount(), id1, counter.getIdCount(id1),
                    id2, counter.getIdCount(id2)));
        } else {
            System.out.println(String.format("rnf-%d, %d-%d, %d-%d",
                    counter.getTotalCount(), id2, counter.getIdCount(id2),
                    id1, counter.getIdCount(id1)));
        }
    }

}
