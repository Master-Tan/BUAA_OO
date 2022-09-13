import java.util.ArrayList;
import java.util.HashSet;

public class LookBuildingDecisionMaker implements DecisionMaker {

    private String atBuilding;
    private RequestPool requestPool;
    private HashSet<MyRequest> allRequest;

    private HashSet<MyRequest> insidePerson;
    private int atFloor;
    private int direction;

    private ArrayList<MyRequest> needPickUp = new ArrayList<>();
    private ArrayList<MyRequest> needPutDown = new ArrayList<>();

    private int min;

    public LookBuildingDecisionMaker(String atBuilding, RequestPool requestPool) {
        this.atBuilding = atBuilding;
        this.requestPool = requestPool;
    }

    @Override
    public void ask(Elevator elevator) {

        this.insidePerson = elevator.getInsidePerson();
        this.atFloor = elevator.getAtFloor();
        this.direction = elevator.getDirection();

        needPickUp.clear();
        needPutDown.clear();

        // 获取请求池,更新本地
        allRequest = requestPool.getAllBuildingRequest(
                atBuilding, insidePerson);



        // 判断电梯是否进入或退出空等
        isOrOutWait();

        // 判断电梯是否转向并转向
        isNeedTurn();

        // 判断应载入人
        getNeedPickUp();


        // 判断应载出人
        for (MyRequest request : insidePerson) {
            if (request.getFromBuilding() == request.getToBuilding() &
                    request.getToFloor() == atFloor) {
                needPutDown.add(request);
            }
            if (request.getToBuilding() != request.getFromBuilding() &
                    request.getChangeFloor() == atFloor) {
                needPutDown.add(request);
            }
        }

    }

    private void getNeedPickUp() {

        // 接最远楼层的
        getFirstNeedPickUp();

        // 先接一个人和与其相同目的地的
        getSecondNeedPickUp();

        // 再接剩下的
        getLastNeedPickUp();

    }

    private void getFirstNeedPickUp() {
        for (MyRequest request : allRequest) {
            if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding)
                    & request.getFromFloor() == atFloor & (request.getToFloor() != atFloor |
                    request.getToBuilding() != atBuilding.charAt(0))) {
                if (direction == 1 & request.getFromBuilding() == request.getToBuilding()) {
                    if (request.getToFloor() > atFloor) {
                        if (needPickUp.size() == 0) { needPickUp.add(request); }
                        else if (Math.abs(needPickUp.get(0).getToFloor() - atFloor) <
                                Math.abs(request.getToFloor() - atFloor)) {
                            needPickUp.remove(0);
                            needPickUp.add(request);
                        }
                    }
                } else if (direction == 1 & request.getFromBuilding() != request.getToBuilding()) {
                    if (request.getChangeFloor() > atFloor) {
                        if (needPickUp.size() == 0) { needPickUp.add(request); }
                        else if (Math.abs(needPickUp.get(0).getToFloor() - atFloor) <
                                Math.abs(request.getToFloor() - atFloor)) {
                            needPickUp.remove(0);
                            needPickUp.add(request);
                        }
                    }
                } else if (direction == -1 & request.getFromBuilding() == request.getToBuilding()) {
                    if (request.getToFloor() < atFloor) {
                        if (needPickUp.size() == 0) { needPickUp.add(request); }
                        else if (Math.abs(needPickUp.get(0).getToFloor() - atFloor) <
                                Math.abs(request.getToFloor() - atFloor)) {
                            needPickUp.remove(0);
                            needPickUp.add(request);
                        }
                    }
                } else if (direction == -1 & request.getFromBuilding() != request.getToBuilding()) {
                    if (request.getChangeFloor() < atFloor) {
                        if (needPickUp.size() == 0) { needPickUp.add(request); }
                        else if (Math.abs(needPickUp.get(0).getToFloor() - atFloor) <
                                Math.abs(request.getToFloor() - atFloor)) {
                            needPickUp.remove(0);
                            needPickUp.add(request);
                        }
                    }
                }
            }
        }
    }

    private void getLastNeedPickUp() {
        for (MyRequest request : allRequest) {
            if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding)
                    & request.getFromFloor() == atFloor & (request.getToFloor() != atFloor |
                    request.getToBuilding() != atBuilding.charAt(0))) {
                if (direction == 1 & request.getFromBuilding() == request.getToBuilding()) {
                    if (request.getToFloor() > atFloor) {
                        if (!needPickUp.contains(request)) { needPickUp.add(request); }
                    }
                } else if (direction == 1 & request.getFromBuilding() != request.getToBuilding()) {
                    if (request.getChangeFloor() > atFloor) {
                        if (!needPickUp.contains(request)) { needPickUp.add(request); }
                    }
                } else if (direction == -1 & request.getFromBuilding() == request.getToBuilding()) {
                    if (request.getToFloor() < atFloor) {
                        if (!needPickUp.contains(request)) { needPickUp.add(request); }
                    }
                } else if (direction == -1 & request.getFromBuilding() != request.getToBuilding()) {
                    if (request.getChangeFloor() < atFloor) {
                        if (!needPickUp.contains(request)) { needPickUp.add(request); }
                    }
                }
            }
        }
    }

    private void getSecondNeedPickUp() {
        for (MyRequest request : allRequest) {
            if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding)
                    & request.getFromFloor() == atFloor & (request.getToFloor() != atFloor |
                    request.getToBuilding() != atBuilding.charAt(0))) {
                if (direction == 1 & request.getFromBuilding() == request.getToBuilding()) {
                    if (request.getToFloor() > atFloor) {
                        if (needPickUp.size() == 0) { needPickUp.add(request); }
                        else if (needPickUp.get(0).getToFloor() == request.getToFloor()) {
                            needPickUp.add(request);
                        }
                    }
                } else if (direction == 1 & request.getFromBuilding() != request.getToBuilding()) {
                    if (request.getChangeFloor() > atFloor) {
                        if (needPickUp.size() == 0) { needPickUp.add(request); }
                        else if (needPickUp.get(0).getChangeFloor() == request.getChangeFloor()) {
                            needPickUp.add(request);
                        }
                    }
                } else if (direction == -1 & request.getFromBuilding() == request.getToBuilding()) {
                    if (request.getToFloor() < atFloor) {
                        if (needPickUp.size() == 0) { needPickUp.add(request); }
                        else if (needPickUp.get(0).getToFloor() == request.getToFloor()) {
                            needPickUp.add(request);
                        }
                    }
                } else if (direction == -1 & request.getFromBuilding() != request.getToBuilding()) {
                    if (request.getChangeFloor() < atFloor) {
                        if (needPickUp.size() == 0) { needPickUp.add(request); }
                        else if (needPickUp.get(0).getChangeFloor() == request.getChangeFloor()) {
                            needPickUp.add(request);
                        }
                    }
                }
            }
        }
    }

    private void isOrOutWait() {

        // 判断电梯是否退出空等
        boolean flag = false;
        for (MyRequest request : allRequest) {
            if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding) &
                    request.getFromBuilding() == request.getToBuilding() &
                    request.getFromFloor() != request.getToFloor()) {
                flag = true;
            }
            if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding) &
                    request.getFromBuilding() != request.getToBuilding() &
                    request.getChangeFloor() != request.getFromFloor()) {
                flag = true;
            }
        }
        if (flag) {
            if (direction == 2) {
                direction = -1;
            } else if (direction == -2) {
                direction = 1;
            }
        }
        // 判断电梯是否空等
        if (!flag & insidePerson.size() == 0) {
            if (direction == 1) {
                direction = 2;
            } else if (direction == -1) {
                direction = -2;
            }
        }

    }

    private void isNeedTurn() {
        if (Math.abs(direction) == 1 & insidePerson.size() == 0) {
            if (direction == 1) {
                boolean flag1 = true;
                for (MyRequest request : allRequest) {
                    if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding) &
                            request.getFromBuilding() == request.getToBuilding() &
                            request.getFromFloor() != request.getToFloor()) {
                        if (request.getFromFloor() > atFloor) {
                            flag1 = false;
                        } else if (request.getFromFloor() == atFloor &
                                request.getFromFloor() < request.getToFloor()) {
                            flag1 = false;
                        }
                    }
                    if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding) &
                            request.getFromBuilding() != request.getToBuilding() &
                            request.getChangeFloor() != request.getFromFloor()) {
                        if (request.getFromFloor() > atFloor) {
                            flag1 = false;
                        } else if (request.getFromFloor() == atFloor &
                                request.getFromFloor() < request.getChangeFloor()) {
                            flag1 = false;
                        }
                    }
                }
                if (flag1) {
                    direction = -1;
                }
            } else {
                boolean flag1 = true;
                for (MyRequest request : allRequest) {
                    if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding) &
                            request.getFromBuilding() == request.getToBuilding() &
                            request.getFromFloor() != request.getToFloor()) {
                        if (request.getFromFloor() < atFloor) {
                            flag1 = false;
                        } else if (request.getFromFloor() == atFloor &
                                request.getFromFloor() > request.getToFloor()) {
                            flag1 = false;
                        }
                    }
                    if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding) &
                            request.getFromBuilding() != request.getToBuilding() &
                            request.getChangeFloor() != request.getFromFloor()) {
                        if (request.getFromFloor() < atFloor) {
                            flag1 = false;
                        } else if (request.getFromFloor() == atFloor &
                                request.getFromFloor() > request.getChangeFloor()) {
                            flag1 = false;
                        }
                    }
                }
                if (flag1) { direction = 1; }
            }
        }
        if (atFloor == 1 & direction == -1) { direction = 1; }
        if (atFloor == 10 & direction == 1) { direction = -1; }
    }

    @Override
    public ArrayList<MyRequest> whoToPickUp() {
        return needPickUp;
    }

    @Override
    public ArrayList<MyRequest> whoToPutDown() {
        return needPutDown;
    }

    @Override
    public int nextDirection() {
        return direction;
    }
}
