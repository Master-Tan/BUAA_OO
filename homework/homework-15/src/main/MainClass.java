package main;

import com.oocourse.uml3.interact.AppRunner;

public class MainClass {
    public static void main(String[] args) throws Exception {
        AppRunner appRunner = AppRunner.newInstance(MyImplementation.class);
        appRunner.run(args);
    }
}