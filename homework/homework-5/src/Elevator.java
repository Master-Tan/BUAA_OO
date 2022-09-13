import com.oocourse.elevator1.PersonRequest;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

public class Elevator extends Thread {

    private boolean isClose = false;

    private String buildingName; // 电梯所属楼层名字
    private int id; // 电梯ID
    private RequestPool requestPool; // 请求池
    private DecisionMaker decisionMaker; // 该电梯对应的决策者
    private int capacity; // 电梯容量
    private int atFloor; // 电梯所在楼层
    private boolean doorOpen; // 电梯门状态
    private HashSet<PersonRequest> insidePerson; // 电梯中的人数
    private int direction; // 电梯运行方向（1为向上，-1为向下,2为向上静止，-2为向下静止）

    private long lastTime;
    private long lastPTime;

    private ReentrantLock thisElevatorLock = new ReentrantLock(); // 当前电梯的锁
    private Condition thisElevatorCondition = thisElevatorLock.newCondition();

    public Elevator(String buildingName, int id,
                    RequestPool requestPool, DecisionMaker decisionMaker) {

        this.buildingName = buildingName;
        this.id = id;
        this.requestPool = requestPool;
        this.decisionMaker = decisionMaker;
        this.capacity = 6;
        this.atFloor = 1;
        this.doorOpen = false;
        this.insidePerson = new HashSet<>();
        this.direction = -2;

        this.lastTime = System.currentTimeMillis();

    }

    @Override
    public void run() {
        // System.out.println(buildingName + "'s Elevator is Running!");
        while (true) {
            decisionMaker.ask(this);
            ArrayList<PersonRequest> whoToPickUp;
            whoToPickUp = decisionMaker.whoToPickUp();
            ArrayList<PersonRequest> whoToPutDown;
            whoToPutDown = decisionMaker.whoToPutDown();

            direction = decisionMaker.nextDirection();
            // System.out.println(buildingName + String.valueOf(direction));


            //            System.out.println(this.buildingName + " Open:" + lastTime);
            // 尝试下客,若有客下且若门没开则开门
            lastPTime = putPeopleDown(whoToPutDown);
            if (lastPTime != -1) {
                lastTime = lastPTime;
            }

            // 尝试上客，门没开则开门
            lastPTime = getPeopleOn(whoToPickUp);
            if (lastPTime != -1) {
                lastTime = lastPTime;
            }

            // 根据接到乘客的状态询问应该怎么走
            decisionMaker.ask(this);
            direction = decisionMaker.nextDirection();
            whoToPickUp = decisionMaker.whoToPickUp();

            // 不同策略此条件可能会更改
            if (!(whoToPickUp.size() != 0 && insidePerson.size() < capacity)) {

                // 判断并尝试关门
                // 门开着就关门
                // 保证电梯运动时门是关的
                // System.out.println(this.buildingName + " Close:" + lastTime);
                lastPTime = closeTheDoor(lastTime);
                if (lastPTime != -1) {
                    lastTime = lastPTime;
                }


                // 电梯尝试按方向运行

                if (!doorOpen) {
                    lastPTime = moveTheElevator(lastTime);
                    if (lastPTime != -1) {
                        lastTime = lastPTime;
                    }
                }
            }


            // 登记是否空等
            if (Math.abs(direction) == 2) {
                requestPool.getElevator().put(this, true);
            } else {
                requestPool.getElevator().put(this, false);
            }

            // 如果请求池没有此楼座请求且输入截止且电梯内没有人，则结束线程
            if (isClose & insidePerson.size() == 0) {
                boolean flag = true;
                for (PersonRequest request : requestPool.getAllRequest(
                        buildingName, insidePerson)) {
                    if (String.valueOf(request.getFromBuilding()).equals(buildingName)) {
                        flag = false;
                    }
                }
                if (flag) {
                    break;
                }
            }

        }

    }

    private long putPeopleDown(ArrayList<PersonRequest> whoToPutDown) {
        long lastTime = -1;
        if (whoToPutDown.size() != 0) {
            for (PersonRequest request : whoToPutDown) {
                // 门没开则开门
                lastPTime = openTheDoor();
                if (lastPTime != -1) {
                    lastTime = lastPTime;
                }

                // 成功放下（送达）乘客
                insidePerson.remove(request);
                OutputThread.println(
                        String.format("OUT-%d-%s-%d-%d",
                                request.getPersonId(), buildingName, atFloor, id));
            }
        }
        return lastTime;
    }

    private long getPeopleOn(ArrayList<PersonRequest> whoToPickUp) {

        long lastTime = -1;

        for (PersonRequest request : whoToPickUp) {
            if (insidePerson.size() < capacity) {
                if (requestPool.removeRequest(request)) { // 若能成功接到乘客（没被别人接走）

                    // 门没开则开门
                    lastPTime = openTheDoor();
                    if (lastPTime != -1) {
                        lastTime = lastPTime;
                    }

                    // 成功接到乘客
                    insidePerson.add(request);
                    OutputThread.println(
                            String.format("IN-%d-%s-%d-%d",
                                    request.getPersonId(), buildingName, atFloor, id));
                }
            }
        }

        return lastTime;
    }

    private long moveTheElevator(long lastTime) {

        long lastTime1 = -1;

        try {
            if (Math.abs(direction) == 1) {
                long curTime = System.currentTimeMillis();
                // 由于开门可以立刻进出，所以开门耗时合并到关门进行wait
                // TimableOutput.println(lastTime);
                // TimableOutput.println(curTime);
                long waitTime = 400 - (curTime - lastTime) + 1;
                thisElevatorLock.lock();
                try {
                    if (thisElevatorCondition.await(waitTime, TimeUnit.MILLISECONDS)) {
                        // 被其他线程唤醒
                        // 运行状态回退
                        atFloor = atFloor;
                    } else {
                        // 指定时间内没有被其他线程唤醒
                        // 成功运行
                        long thisTime = System.currentTimeMillis();
                        if (thisTime - lastTime > 400) {
                            atFloor += direction;
                            lastTime1 = OutputThread.println(
                                    String.format("ARRIVE-%s-%d-%d",
                                            buildingName, atFloor, id));
                        }
                    }
                } finally {
                    thisElevatorLock.unlock();
                }

            }
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        return lastTime1;
    }

    private long closeTheDoor(long lastTime) {

        long lastTime1 = -1;

        if (doorOpen) {
            try {
                long curTime = System.currentTimeMillis();
                // 由于开门可以立刻进出，所以开门耗时合并到关门进行wait

                long waitTime = 400 - (curTime - lastTime) + 1;
                //                System.out.println("lastTime " + lastTime);
                //                System.out.println("cutTime " + curTime);
                //                System.out.println("waitTime " + waitTime);
                thisElevatorLock.lock();
                try {
                    if (thisElevatorCondition.await(waitTime, TimeUnit.MILLISECONDS)) {
                        // 被其他线程唤醒
                        // 关门状态回退
                        doorOpen = true;
                    } else {
                        // 指定时间内没有被其他线程唤醒
                        // 成功关门
                        long thisTime = System.currentTimeMillis();
                        if (thisTime - lastTime > 400) {
                            doorOpen = false;
                            lastTime1 = OutputThread.println(
                                    String.format("CLOSE-%s-%d-%d",
                                            buildingName, atFloor, id));
                        }
                    }
                } finally {
                    thisElevatorLock.unlock();
                }

            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        return lastTime1;
    }

    private long openTheDoor() {
        long lastTime = -1;
        if (!doorOpen) {
            // 成功开门
            doorOpen = true;
            lastTime = OutputThread.println(
                    String.format("OPEN-%s-%d-%d", buildingName, atFloor, id));
            // Thread.sleep(200);
        }
        return lastTime;
    }

    public void setClose(boolean close) {
        isClose = close;
    }

    public int getAtFloor() {
        return atFloor;
    }

    public HashSet<PersonRequest> getInsidePerson() {
        return insidePerson;
    }

    public int getDirection() {
        return direction;
    }

    public ReentrantLock getThisElevatorLock() {
        return thisElevatorLock;
    }

    public Condition getThisElevatorCondition() {
        return thisElevatorCondition;
    }
}
