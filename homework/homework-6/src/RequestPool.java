import java.util.HashSet;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

// 中枢类
// 线程安全类
public class RequestPool {

    // 方法锁
    private final ReentrantLock lock = new ReentrantLock();

    private final Condition condition = lock.newCondition();

    // 请求池
    private HashSet<MyRequest> personRequests = new HashSet<>();

    // 电梯表
    private HashSet<Elevator> elevators = new HashSet<>();

    private boolean isClose = false;

    private int min;

    private final ReadWriteLock rwElevatorLock = new ReentrantReadWriteLock();
    private final Lock relevatorLock = rwElevatorLock.readLock();
    private final Lock welevatorLock = rwElevatorLock.writeLock();

    public void addPersonRequest(MyRequest request) {

        getChangeFloor(request);

        relevatorLock.lock();
        try {
            for (Elevator elevator : elevators) {
                elevator.getThisElevatorLock().lock();
                elevator.getThisElevatorCondition().signalAll();
                elevator.getThisElevatorLock().unlock();
            }
        } finally {
            relevatorLock.unlock();
        }

        lock.lock();
        try {
            personRequests.add(request);
            // TimableOutput.println("addRequest");
            condition.signalAll();
            // System.out.println(request);
        } finally {
            lock.unlock();
        }
    }

    private void getChangeFloor(MyRequest request) {
        if (request.getFromBuilding() != request.getToBuilding()) {
            min = (Math.abs(request.getFromFloor() - request.getChangeFloor()) +
                    Math.abs(request.getToFloor() - request.getChangeFloor()));
            for (Elevator ele : this.getElevators()) {
                if (ele instanceof FloorElevator) {
                    if ((((((FloorElevator) ele).getSwitchInfo() >>
                            (request.getFromBuilding() - 'A')) & 1) +
                            ((((FloorElevator) ele).getSwitchInfo() >>
                                    (request.getToBuilding() - 'A')) & 1)) == 2) {
                        if ((Math.abs(request.getFromFloor() - ele.getAtFloor()) +
                                Math.abs(request.getToFloor() - ele.getAtFloor())) < min) {
                            lock.lock();
                            try {
                                request.setChangeFloor(ele.getAtFloor());
                            } finally {
                                lock.unlock();
                            }
                            min = (Math.abs(request.getFromFloor() - ele.getAtFloor()) +
                                    Math.abs(request.getToFloor() - ele.getAtFloor()));
                        }
                    }
                }
            }
        }
    }

    public boolean removePersonRequest(MyRequest request) {
        lock.lock();
        try {
            if (personRequests.contains(request)) {
                personRequests.remove(request);
                return true;
            } else {
                return false;
            }
        } finally {
            lock.unlock();
        }
    }

    public HashSet<MyRequest> getAllRequest() {

        lock.lock();
        try {
            HashSet<MyRequest> allRequest = new HashSet<>();
            for (MyRequest request : personRequests) {
                allRequest.add(request);
            }
            // TimableOutput.println(buildingName + " Return!");
            return allRequest;
        } finally {
            lock.unlock();
        }
    }

    public HashSet<MyRequest> getAllBuildingRequest(String buildingName,
                                                    HashSet<MyRequest> insidePerson) {

        lock.lock();
        try {
            boolean flag = false;
            for (MyRequest request : personRequests) {
                if (request.getFromBuilding() == request.getToBuilding()) {
                    if (String.valueOf(request.getFromBuilding()).equals(buildingName) &
                            request.getFromFloor() != request.getToFloor()) {
                        flag = true;
                    }
                }
                if (request.getFromBuilding() != request.getToBuilding()) {
                    if (String.valueOf(request.getFromBuilding()).equals(buildingName) &
                            request.getFromFloor() != request.getChangeFloor()) {
                        flag = true;
                    }
                }
            }
            // TimableOutput.println(buildingName + " " + flag);
            if (!flag & insidePerson.size() == 0) {
                boolean willNotifyAll = false;

                relevatorLock.lock();
                try {
                    for (Elevator elevator : elevators) {
                        for (MyRequest request : elevator.getInsidePerson()) {
                            if (elevator instanceof BuildingElevator) {
                                if (request.getFromBuilding() != request.getToBuilding()) {
                                    willNotifyAll = true;
                                }
                            }
                            if (elevator instanceof FloorElevator) {
                                if (request.getFromFloor() != request.getToFloor()) {
                                    willNotifyAll = true;
                                }
                            }
                        }
                    }
                } finally {
                    relevatorLock.unlock();
                }


                for (MyRequest request : personRequests) {
                    if (request.getFromBuilding() != request.getToBuilding() &
                            request.getFromFloor() != request.getChangeFloor()) {
                        willNotifyAll = true;
                    }
                }

                if (!isClose | willNotifyAll) {
                    // TimableOutput.println(buildingName + " need Sleep!");
                    try {
                        // TimableOutput.println(buildingName + " Sleep!!");
                        condition.await();
                        // TimableOutput.println(buildingName + " Awake!!");
                    } catch (InterruptedException e) {
                        e.printStackTrace();
                    }
                }
            }
            HashSet<MyRequest> allRequest = new HashSet<>();
            for (MyRequest request : personRequests) { allRequest.add(request); }
            // TimableOutput.println(buildingName + " Return!");
            return allRequest;
        } finally {
            // TimableOutput.println(buildingName + " unlocked!");
            lock.unlock();
        }
    }

    public HashSet<MyRequest> getAllFloorRequest(int atFloor,
                                                 HashSet<MyRequest> insidePerson) {
        // TODO 修改wait条件
        lock.lock();
        try {
            boolean flag = false;
            for (MyRequest request : personRequests) {
                if (request.getFromFloor() == atFloor &
                        request.getFromBuilding() != request.getToBuilding()) {
                    flag = true;
                }
            }
            // TimableOutput.println(buildingName + " " + flag);
            if (!flag & insidePerson.size() == 0) {
                boolean willNotifyAll = false;

                relevatorLock.lock();
                try {
                    for (Elevator elevator : elevators) {
                        for (MyRequest request : elevator.getInsidePerson()) {
                            if (elevator instanceof BuildingElevator) {
                                if (request.getFromBuilding() != request.getToBuilding()) {
                                    willNotifyAll = true;
                                }
                            }
                            if (elevator instanceof FloorElevator) {
                                if (request.getFromFloor() != request.getToFloor()) {
                                    willNotifyAll = true;
                                }
                            }
                        }
                    }
                } finally {
                    relevatorLock.unlock();
                }


                for (MyRequest request : personRequests) {
                    if (request.getFromBuilding() != request.getToBuilding() &
                            request.getFromFloor() != request.getChangeFloor()) {
                        willNotifyAll = true;
                    }
                }

                if (!isClose | willNotifyAll) {
                    // TimableOutput.println(buildingName + " need Sleep!");
                    try {
                        // TimableOutput.println(buildingName + " Sleep!!");
                        condition.await();
                        // TimableOutput.println(buildingName + " Awake!!");
                    } catch (InterruptedException e) {
                        e.printStackTrace();
                    }
                }
            }
            HashSet<MyRequest> allRequest = new HashSet<>();
            for (MyRequest request : personRequests) {
                allRequest.add(request);
            }
            // TimableOutput.println(buildingName + " Return!");
            return allRequest;
        } finally {
            // TimableOutput.println(buildingName + " unlocked!");
            lock.unlock();
        }
    }

    public void close() {
        lock.lock();
        try {
            isClose = true;
            condition.signalAll();

            relevatorLock.lock();
            try {
                for (Elevator elevator : elevators) {
                    elevator.setClose(true);
                    // System.out.println("Elevator " + elevator.getName() + " is closeing!");
                }
            } finally {
                relevatorLock.unlock();
            }

        } finally {
            lock.unlock();
        }
    }

    public void addElevators(Elevator elevator) {

        // 更新所有乘客换乘楼层
        HashSet<MyRequest> allRequest = this.getAllRequest();
        for (MyRequest request : allRequest) {
            getChangeFloor(request);
        }

        welevatorLock.lock();
        try {
            elevators.add(elevator);
        } finally {
            welevatorLock.unlock();
        }

    }

    public HashSet<Elevator> getElevators() {
        HashSet<Elevator> outElevators = new HashSet<>();
        relevatorLock.lock();
        try {
            for (Elevator elevator : elevators) {
                outElevators.add(elevator);
            }
        } finally {
            relevatorLock.unlock();
        }
        return outElevators;
    }

    public void addNotLockedPersonRequest(MyRequest request) {

        getChangeFloor(request);

        relevatorLock.lock();
        try {
            for (Elevator elevator : elevators) {
                elevator.getThisElevatorLock().lock();
                elevator.getThisElevatorCondition().signalAll();
                elevator.getThisElevatorLock().unlock();
            }
        } finally {
            relevatorLock.unlock();
        }

        personRequests.add(request);
        // TimableOutput.println("addRequest");
        condition.signalAll();
        // System.out.println(request);
    }

    public boolean removeNotLockedPersonRequest(MyRequest request) {
        if (personRequests.contains(request)) {
            personRequests.remove(request);
            return true;
        } else {
            return false;
        }
    }

    public ReentrantLock getLock() {
        return lock;
    }

    public void addElevatorRequest() {
        relevatorLock.lock();
        try {
            for (Elevator elevator : elevators) {
                elevator.getThisElevatorLock().lock();
                elevator.getThisElevatorCondition().signalAll();
                elevator.getThisElevatorLock().unlock();
            }
        } finally {
            relevatorLock.unlock();
        }
    }
}
