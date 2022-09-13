import com.oocourse.elevator1.PersonRequest;

import java.util.HashMap;
import java.util.HashSet;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

// 中枢类
// 线程安全类
public class RequestPool {

    // 空等锁
    private final ReentrantLock lock = new ReentrantLock();

    private final Condition condition = lock.newCondition();

    // 请求池
    private HashSet<PersonRequest> personRequests = new HashSet<>();

    // 空等表
    private HashMap<Elevator, Boolean> elevator = new HashMap<>();

    private boolean isClose = false;

    public void addRequest(PersonRequest request) {
        lock.lock();
        for (Elevator elevator : elevator.keySet()) {
            elevator.getThisElevatorLock().lock();
            elevator.getThisElevatorCondition().signalAll();
            elevator.getThisElevatorLock().unlock();
        }
        try {
            personRequests.add(request);
            // TimableOutput.println("addRequest");
            condition.signalAll();
            // System.out.println(request);
        } finally {
            lock.unlock();
        }
    }

    public boolean removeRequest(PersonRequest request) {
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

    public HashSet<PersonRequest> getAllRequest(String buildingName,
                                                HashSet<PersonRequest> insidePerson) {
        lock.lock();
        try {
            boolean flag = false;
            for (PersonRequest request : personRequests) {
                if (String.valueOf(request.getFromBuilding()).equals(buildingName)) {
                    flag = true;
                }
            }
            // TimableOutput.println(buildingName + " " + flag);
            if (!flag & insidePerson.size() == 0 & !isClose) {
                // TimableOutput.println(buildingName + " need Sleep!");
                try {
                    // TimableOutput.println(buildingName + " Sleep!!");
                    condition.await();
                    // TimableOutput.println(buildingName + " Awake!!");
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }

            }
            HashSet<PersonRequest> allRequest = new HashSet<>();
            for (PersonRequest request : personRequests) {
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
            for (Elevator elevator : elevator.keySet()) {
                elevator.setClose(true);
                // System.out.println("Elevator " + elevator.getName() + " is closeing!");
            }
        } finally {
            lock.unlock();
        }
    }

    public HashMap<Elevator, Boolean> getElevator() {
        return elevator;
    }

}
