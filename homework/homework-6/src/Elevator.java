import java.util.HashSet;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

public interface Elevator {

    void setClose(boolean close);

    int getAtFloor();

    HashSet<MyRequest> getInsidePerson();

    int getDirection();

    ReentrantLock getThisElevatorLock();

    Condition getThisElevatorCondition();

    String getAtBuilding();

}
