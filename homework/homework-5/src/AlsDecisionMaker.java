import com.oocourse.elevator1.PersonRequest;

import java.util.ArrayList;
import java.util.HashSet;

public class AlsDecisionMaker implements DecisionMaker {

    private String buildName;
    private int id;
    private RequestPool requestPool;

    private HashSet<PersonRequest> insidePerson;
    private int atFloor;
    private int direction;

    private ArrayList<PersonRequest> needPickUp = new ArrayList<>();
    private ArrayList<PersonRequest> needPutDown = new ArrayList<>();

    public AlsDecisionMaker(String buildName, int id, RequestPool requestPool) {
        this.buildName = buildName;
        this.id = id;
        this.requestPool = requestPool;
    }

    @Override
    public void ask(Elevator elevator) {

        this.insidePerson = elevator.getInsidePerson();
        this.atFloor = elevator.getAtFloor();
        this.direction = elevator.getDirection();

    }

    @Override
    public ArrayList<PersonRequest> whoToPickUp() {
        return needPickUp;
    }

    @Override
    public ArrayList<PersonRequest> whoToPutDown() {
        return needPutDown;
    }

    @Override
    public int nextDirection() {
        return 0;
    }

}
