import com.oocourse.elevator1.PersonRequest;

import java.util.ArrayList;
import java.util.HashSet;

public class LookDecisionMaker implements DecisionMaker {

    private String buildName;
    private int id;
    private RequestPool requestPool;

    private HashSet<PersonRequest> insidePerson;
    private int atFloor;
    private int direction;

    private ArrayList<PersonRequest> needPickUp = new ArrayList<>();
    private ArrayList<PersonRequest> needPutDown = new ArrayList<>();

    public LookDecisionMaker(String buildName, int id, RequestPool requestPool) {
        this.buildName = buildName;
        this.id = id;
        this.requestPool = requestPool;
    }

    @Override
    public void ask(Elevator elevator) {

        this.insidePerson = elevator.getInsidePerson();
        this.atFloor = elevator.getAtFloor();
        this.direction = elevator.getDirection();

        needPickUp.clear();
        needPutDown.clear();

        // 获取请求池
        HashSet<PersonRequest> allRequest = requestPool.getAllRequest(
                buildName, insidePerson);

        // 判断电梯是否退出空等
        boolean flag = false;
        for (PersonRequest request : allRequest) {
            if (String.valueOf(request.getFromBuilding()).equals(this.buildName) &
                    request.getFromFloor() != request.getToFloor()) {
                flag = true;
            }
        }
        if (flag) {
            if (direction == 2) {
                direction = -1;
            }
            else if (direction == -2) {
                direction = 1;
            }
        }
        // 判断电梯是否空等
        if (!flag & insidePerson.size() == 0) {
            if (direction == 1) {
                direction = 2;
            }
            else if (direction == -1) {
                direction = -2;
            }
        }

        // 判断电梯是否转向
        isNeedTurn(allRequest);

        // 判断应载入人
        for (PersonRequest request : allRequest) {
            if (String.valueOf(request.getFromBuilding()).equals(this.buildName)
                    & request.getFromFloor() == atFloor & request.getToFloor() != atFloor) {
                if (direction == 1) {
                    if (request.getToFloor() > atFloor) {
                        needPickUp.add(request);
                    }
                } else if (direction == -1) {
                    if (request.getToFloor() < atFloor) {
                        needPickUp.add(request);
                    }
                }
            }
        }
        // 判断应载出人
        for (PersonRequest request : insidePerson) {
            if (request.getToFloor() == atFloor) {
                needPutDown.add(request);
            }
        }

    }

    private void isNeedTurn(HashSet<PersonRequest> allRequest) {
        if (Math.abs(direction) == 1 & insidePerson.size() == 0) {
            if (direction == 1) {
                boolean flag1 = true;
                for (PersonRequest request : allRequest) {
                    if (String.valueOf(request.getFromBuilding()).equals(this.buildName)  &
                            request.getFromFloor() != request.getToFloor()) {
                        if (request.getFromFloor() > atFloor) {
                            flag1 = false;
                        } else if (request.getFromFloor() == atFloor &
                                request.getFromFloor() < request.getToFloor()) {
                            flag1 = false;
                        }
                    }
                }
                if (flag1) {
                    direction = -1;
                }
            }
            else {
                boolean flag1 = true;
                for (PersonRequest request : allRequest) {
                    if (String.valueOf(request.getFromBuilding()).equals(this.buildName) &
                            request.getFromFloor() != request.getToFloor()) {
                        if (request.getFromFloor() < atFloor) {
                            flag1 = false;
                        }
                        else if (request.getFromFloor() == atFloor &
                                request.getFromFloor() > request.getToFloor()) {
                            flag1 = false;
                        }
                    }
                }
                if (flag1) {
                    direction = 1;
                }
            }
        }
        if (atFloor == 1 & direction == -1) {
            direction = 1;
        }
        if (atFloor == 10 & direction == 1) {
            direction = -1;
        }
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
        return direction;
    }
}
