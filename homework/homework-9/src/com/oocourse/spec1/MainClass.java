package com.oocourse.spec1;

import com.oocourse.spec1.main.MyGroup;
import com.oocourse.spec1.main.MyNetwork;
import com.oocourse.spec1.main.MyPerson;
import com.oocourse.spec1.main.Runner;

public class MainClass {
    public static void main(String[] args) throws Exception {
        Runner runner = new Runner(MyPerson.class, MyNetwork.class, MyGroup.class);
        runner.run();
    }
}
