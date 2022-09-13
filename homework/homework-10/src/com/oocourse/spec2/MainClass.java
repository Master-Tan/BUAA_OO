package com.oocourse.spec2;

import com.oocourse.spec2.main.MyGroup;
import com.oocourse.spec2.main.MyMessage;
import com.oocourse.spec2.main.MyNetwork;
import com.oocourse.spec2.main.MyPerson;
import com.oocourse.spec2.main.Runner;

public class MainClass {
    public static void main(String[] args) throws Exception {
        Runner runner = new Runner(MyPerson.class, MyNetwork.class, MyGroup.class, MyMessage.class);
        runner.run();
    }
}
