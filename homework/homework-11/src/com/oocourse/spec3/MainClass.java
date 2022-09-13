package com.oocourse.spec3;

import com.oocourse.spec3.main.MyEmojiMessage;
import com.oocourse.spec3.main.MyGroup;
import com.oocourse.spec3.main.MyMessage;
import com.oocourse.spec3.main.MyNetwork;
import com.oocourse.spec3.main.MyNoticeMessage;
import com.oocourse.spec3.main.MyPerson;
import com.oocourse.spec3.main.MyRedEnvelopeMessage;
import com.oocourse.spec3.main.Runner;

public class MainClass {
    public static void main(String[] args) throws Exception {
        Runner runner = new Runner(MyPerson.class, MyNetwork.class, MyGroup.class,MyMessage.class,
                MyEmojiMessage.class, MyNoticeMessage.class, MyRedEnvelopeMessage.class);
        runner.run();
    }
}
