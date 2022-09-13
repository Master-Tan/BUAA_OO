import java.util.ArrayList;
import java.util.HashSet;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

public class BuildingElevator extends Thread implements Elevator {

    private boolean isClose = false;

    private String atBuilding; // 电梯所属楼层名字
    private int id; // 电梯ID
    private RequestPool requestPool; // 请求池
    private DecisionMaker decisionMaker; // 该电梯对应的决策者
    private int capacity; // 电梯容量
    private long speed; // 电梯速度
    private int atFloor; // 电梯所在楼层
    private boolean doorOpen; // 电梯门状态
    private HashSet<MyRequest> insidePerson; // 电梯中的人数
    private int direction; // 电梯运行方向（1为向上，-1为向下,2为向上静止，-2为向下静止）

    private long lastTime;
    private long lastPTime;

    private ReentrantLock thisElevatorLock = new ReentrantLock(); // 当前电梯的锁
    private Condition thisElevatorCondition = thisElevatorLock.newCondition();

    private ReentrantLock thisInsidePersonLock = new ReentrantLock(); // 当前电梯内部人员的锁
    private Condition thisInsidePersonCondition = thisInsidePersonLock.newCondition();

    private boolean flag;

    public BuildingElevator(String atBuilding, int id, int capacity,
                            long speed, RequestPool requestPool, DecisionMaker decisionMaker) {

        this.atBuilding = atBuilding;
        this.id = id;
        this.requestPool = requestPool;
        this.decisionMaker = decisionMaker;
        this.capacity = capacity;
        this.speed = speed;
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
            // System.out.println(id + " ask1");
            ArrayList<MyRequest> whoToPickUp;
            whoToPickUp = decisionMaker.whoToPickUp();
            ArrayList<MyRequest> whoToPutDown;
            whoToPutDown = decisionMaker.whoToPutDown();

            direction = decisionMaker.nextDirection();
            // System.out.println(buildingName + String.valueOf(direction));


            // System.out.println(this.buildingName + " Open:" + lastTime);
            // 尝试下客,若有客下且若门没开则开门
            lastPTime = putPeopleDown(whoToPutDown);
            checkTime();
            // System.out.println(id + " down");

            // 尝试上客，若有客上且门没开则开门
            lastPTime = getPeopleOn(whoToPickUp);
            // System.out.println(id + " up");
            checkTime();

            // 根据接到乘客的状态询问应该怎么走
            // System.out.println(id + " ask2");
            decisionMaker.ask(this);
            // System.out.println(id + " ask3");
            direction = decisionMaker.nextDirection();
            whoToPickUp = decisionMaker.whoToPickUp();
            // System.out.println(id + " " + direction);

            // 不同策略此条件可能会更改
            if (!(whoToPickUp.size() != 0 && insidePerson.size() < capacity)) {

                // 判断并尝试关门
                // 门开着就关门
                // 保证电梯运动时门是关的
                // System.out.println(this.buildingName + " Close:" + lastTime);
                lastPTime = closeTheDoor(lastTime);
                checkTime();


                // 电梯尝试按方向运行

                if (!doorOpen) {
                    lastPTime = moveTheElevator(lastTime);
                    checkTime();
                }
            }

            // 如果请求池没有此楼座请求且输入截止且电梯内没有人，则结束线程
            if (endTheThread()) {
                break;
            }


        }

    }

    private boolean endTheThread() {
        if (isClose & insidePerson.size() == 0) {

            flag = true;

            requestPool.getLock().lock();
            try {
                for (Elevator elevator : requestPool.getElevators()) {
                    if (elevator instanceof FloorElevator) {
                        for (MyRequest request : elevator.getInsidePerson()) {
                            if ((String.valueOf(request.getToBuilding()).equals(atBuilding)) &
                                    elevator.getAtFloor() != request.getToFloor()) {
                                flag = false;
                            }
                        }
                    }
                    if (elevator instanceof BuildingElevator) {
                        if (!elevator.getAtBuilding().equals(atBuilding)) {
                            for (MyRequest request : elevator.getInsidePerson()) {
                                if (String.valueOf(request.getToBuilding()).equals(atBuilding)) {
                                    if (request.getToFloor() != request.getChangeFloor()) {
                                        flag = false;
                                    }
                                }
                            }
                        }
                    }
                }
                // System.out.println(id + " " + flag);
                for (MyRequest request : requestPool.getNotLockedAllRequest()) {
                    checkFlag(request);
                }
            } finally {
                requestPool.getLock().unlock();
            }

            if (flag) {
                while (doorOpen) {
                    lastPTime = closeTheDoor(lastTime);
                    checkTime();
                }
                // System.out.println(id + " break!!");
                return true;
            }
        }
        return false;
    }

    private void checkFlag(MyRequest request) {
        if (String.valueOf(request.getFromBuilding()).equals(atBuilding)) {
            if (request.getFromBuilding() == request.getToBuilding() &
                    request.getFromFloor() != request.getToFloor()) {
                flag = false;
            }
            if (request.getFromBuilding() != request.getToBuilding() &
                    request.getFromFloor() != request.getChangeFloor()) {
                flag = false;
            }
        } else if (String.valueOf(request.getToBuilding()).equals(atBuilding)) {
            if (request.getFromBuilding() == request.getToBuilding() &
                    request.getFromFloor() != request.getToFloor()) {
                flag = false;
            }
            if (request.getFromBuilding() != request.getToBuilding() &
                    request.getToFloor() != request.getChangeFloor()) {
                flag = false;
            }
        }
    }

    private void checkTime() {
        if (lastPTime != -1) {
            lastTime = lastPTime;
        }
    }

    private long putPeopleDown(ArrayList<MyRequest> whoToPutDown) {
        long lastTime = -1;
        if (whoToPutDown.size() != 0) {
            for (MyRequest request : whoToPutDown) {
                // 门没开则开门
                lastPTime = openTheDoor();
                if (lastPTime != -1) {
                    lastTime = lastPTime;
                }

                // 成功放下（送达）乘客
                // 注意线程安全

                OutputThread.println(
                        String.format("OUT-%d-%s-%d-%d",
                                request.getPersonId(), atBuilding, atFloor, id));
                // System.out.println("changefloor" + request.getChangeFloor());

                requestPool.getLock().lock();
                try {

                    MyRequest addRequest = new MyRequest(atFloor, request.getToFloor(),
                            atBuilding, String.valueOf(request.getToBuilding()),
                            request.getPersonId());

                    addRequest.setChangeFloor(request.getChangeFloor());

                    thisInsidePersonLock.lock();
                    try {

                        insidePerson.remove(request);
                        if (!String.valueOf(request.getToBuilding()).equals(atBuilding)) {
                            requestPool.addNotLockedPersonRequest(addRequest);
                            // System.out.println("A PersonRequest:    " + addRequest);
                        }

                    } finally {
                        thisInsidePersonLock.unlock();
                    }
                } finally {
                    requestPool.getLock().unlock();
                }

            }
        }
        return lastTime;
    }

    private long getPeopleOn(ArrayList<MyRequest> whoToPickUp) {

        long lastTime = -1;

        for (MyRequest request : whoToPickUp) {
            if (insidePerson.size() < capacity) {

                boolean isMoved;

                // 成功接到乘客
                // 注意线程安全
                requestPool.getLock().lock();
                try {
                    thisInsidePersonLock.lock();
                    // System.out.println(id + " locked1");
                    try {
                        isMoved = requestPool.removeNotLockedPersonRequest(request);
                        if (isMoved) {
                            insidePerson.add(request);
                        }
                    } finally {
                        thisInsidePersonLock.unlock();
                        // System.out.println(id + " unlocked1");
                    }
                } finally {
                    requestPool.getLock().unlock();
                }

                if (isMoved) { // 若能成功接到乘客（没被别人接走）

                    // 门没开则开门
                    lastPTime = openTheDoor();
                    if (lastPTime != -1) {
                        lastTime = lastPTime;
                    }

                    OutputThread.println(
                            String.format("IN-%d-%s-%d-%d",
                                    request.getPersonId(), atBuilding, atFloor, id));
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
                long waitTime = speed - (curTime - lastTime) + 1;
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
                        if (thisTime - lastTime > speed) {
                            atFloor += direction;
                            lastTime1 = OutputThread.println(
                                    String.format("ARRIVE-%s-%d-%d",
                                            atBuilding, atFloor, id));
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
                // System.out.println("lastTime " + lastTime);
                // System.out.println("cutTime " + curTime);
                // System.out.println("waitTime " + waitTime);
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
                                            atBuilding, atFloor, id));
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
                    String.format("OPEN-%s-%d-%d", atBuilding, atFloor, id));
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

    public HashSet<MyRequest> getInsidePerson() {
        thisInsidePersonLock.lock();
        try {
            HashSet<MyRequest> outInsidePerson = new HashSet<>();
            for (MyRequest person : insidePerson) {
                outInsidePerson.add(person);
            }
            return outInsidePerson;
        } finally {
            thisInsidePersonLock.unlock();
        }
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

    public String getAtBuilding() {
        return atBuilding;
    }
}
