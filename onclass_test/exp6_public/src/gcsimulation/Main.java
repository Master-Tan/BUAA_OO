package gcsimulation;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        MyJvm myJvm = new MyJvm();
        System.out.println("Start JVM Garbage Collection Simulation.");
        Scanner scanner = new Scanner(System.in);
        while (scanner.hasNext()) {
            String operation = scanner.next();
            if (operation.equals("CreateObject")) {
                int count = scanner.nextInt();
                myJvm.createObject(count);
                System.out.println("Create " + count + " Objects.");
            } else if (operation.equals("SetUnreferenced")) {
                List<Integer> unrefList = new ArrayList<>();
                while (scanner.hasNextInt()) {
                    int id = scanner.nextInt();
                    unrefList.add(id);
                    System.out.println("Set id: " + id + " Unreferenced Object.");
                }
                myJvm.setUnreferenced(unrefList);
            } else if (operation.equals("RemoveUnreferenced")) {
                myJvm.removeUnreferenced();
                System.out.println("Remove Unreferenced Object.");
            } else if (operation.equals("MinorGC")) {
                myJvm.minorGC();
                System.out.println("Execute Minor Garbage Collection.");
            } else if (operation.equals("MajorGC")) {
                myJvm.majorGC();
                System.out.println("Execute Major Garbage Collection.");
            } else if (operation.equals("SnapShot")) {
                myJvm.getSnapShot();
            } else {
                System.err.println("Invalid operation.");
            }
        }
        scanner.close();
        System.out.println("End of JVM Garbage Collection Simulation.");
    }
}
