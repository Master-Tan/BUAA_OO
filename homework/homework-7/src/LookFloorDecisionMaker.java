import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;

public class LookFloorDecisionMaker implements DecisionMaker {

    private int atFloor;
    private int switchInfo;
    private RequestPool requestPool;

    private HashSet<MyRequest> insidePerson;
    private String atBuilding;
    private int direction;

    private ArrayList<MyRequest> needPickUp = new ArrayList<>();
    private ArrayList<MyRequest> needPutDown = new ArrayList<>();

    private ArrayList<String> buildNameList = new ArrayList<>(
            Arrays.asList("A", "B", "C", "D", "E")); // 所有的楼号

    public LookFloorDecisionMaker(int atFloor, int switchInfo, RequestPool requestPool) {
        this.atFloor = atFloor;
        this.switchInfo = switchInfo;
        this.requestPool = requestPool;
    }

    @Override
    public void ask(Elevator elevator) {

        this.insidePerson = elevator.getInsidePerson();
        this.atBuilding = elevator.getAtBuilding();
        this.direction = elevator.getDirection();

        needPickUp.clear();
        needPutDown.clear();

        // 获取请求池
        HashSet<MyRequest> allRequest = requestPool.getAllFloorRequest(
                atFloor, insidePerson, switchInfo);

        // 判断电梯是否进入或退出空等
        isOrOutWait(allRequest);

        // 判断电梯是否转向并转向
        isNeedTurn(allRequest);

        if (((switchInfo >> (atBuilding.charAt(0) - 'A')) & 1) == 1) {

            // 判断应载入人

            // 先接距离最远的
            for (MyRequest request : allRequest) {
                if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding)
                        & request.getFromFloor() == atFloor
                        & request.getFromBuilding() != request.getToBuilding()
                        & ((switchInfo >> (request.getFromBuilding() - 'A')) & 1) +
                        ((switchInfo >> (request.getToBuilding() - 'A')) & 1) == 2) {
                    // 能上就上
                    if (needPickUp.size() == 0) {
                        needPickUp.add(request);
                    } else if (Math.abs(needPickUp.get(0).getToBuilding() - atBuilding.charAt(0)) <
                            Math.abs(request.getToBuilding() - atBuilding.charAt(0))) {
                        needPickUp.remove(0);
                        needPickUp.add(request);
                    }
                }
            }
            // 先接一个人和与其相同目的地的
            for (MyRequest request : allRequest) {
                if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding)
                        & request.getFromFloor() == atFloor
                        & request.getFromBuilding() != request.getToBuilding()
                        & ((switchInfo >> (request.getFromBuilding() - 'A')) & 1) +
                        ((switchInfo >> (request.getToBuilding() - 'A')) & 1) == 2) {
                    // 能上就上
                    if (needPickUp.size() == 0) {
                        needPickUp.add(request);
                    } else if (needPickUp.get(0).getToBuilding() == request.getToBuilding()) {
                        needPickUp.add(request);
                    }
                }
            }
            // 再接剩下的
            for (MyRequest request : allRequest) {
                if (String.valueOf(request.getFromBuilding()).equals(this.atBuilding)
                        & request.getFromFloor() == atFloor
                        & request.getFromBuilding() != request.getToBuilding()
                        & ((switchInfo >> (request.getFromBuilding() - 'A')) & 1) +
                        ((switchInfo >> (request.getToBuilding() - 'A')) & 1) == 2) {
                    // 能上就上
                    if (!needPickUp.contains(request)) {
                        needPickUp.add(request);
                    }
                }
            }
            // 判断应载出人
            for (MyRequest request : insidePerson) {
                if (String.valueOf(request.getToBuilding()).equals(atBuilding)) {
                    needPutDown.add(request);
                }
            }

        }

    }

    private void isOrOutWait(HashSet<MyRequest> allRequest) {

        boolean flag = false;
        for (MyRequest request : allRequest) {
            if (request.getFromFloor() == atFloor &
                    request.getFromBuilding() != request.getToBuilding()) {
                if (((switchInfo >> (request.getFromBuilding() - 'A')) & 1) +
                        ((switchInfo >> (request.getToBuilding() - 'A')) & 1) == 2) {
                    flag = true;
                }
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

    private void isNeedTurn(HashSet<MyRequest> allRequest) {
        if (Math.abs(direction) == 1 & insidePerson.size() == 0) {
            if (direction == 1) {
                boolean flag1 = true;
                for (MyRequest request : allRequest) {

                    if (request.getFromFloor() == atFloor &
                            request.getFromBuilding() != request.getToBuilding() &
                            ((switchInfo >> (request.getFromBuilding() - 'A')) & 1) +
                                    ((switchInfo >> (request.getToBuilding() - 'A')) & 1) == 2) {
                        if ((buildNameList.indexOf(atBuilding) + 5 - buildNameList.indexOf(
                                String.valueOf(request.getFromBuilding()))) % 5 >= 3) {
                            flag1 = false;
                        } else if (String.valueOf(request.getFromBuilding()).equals(atBuilding) &
                                (buildNameList.indexOf(atBuilding) + 5 - buildNameList.indexOf(
                                        String.valueOf(request.getToBuilding()))) % 5 >= 3) {
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

                    // System.out.println("atbuilding " + buildNameList.indexOf(atBuilding));
                    // System.out.println("getFromBuilding " +
                    // buildNameList.indexOf(String.valueOf(request.getFromBuilding())));

                    if (request.getFromFloor() == atFloor &
                            request.getFromBuilding() != request.getToBuilding() &
                            ((switchInfo >> (request.getFromBuilding() - 'A')) & 1) +
                                    ((switchInfo >> (request.getToBuilding() - 'A')) & 1) == 2) {
                        if (!String.valueOf(request.getFromBuilding()).equals(atBuilding) &
                                (buildNameList.indexOf(atBuilding) + 5 - buildNameList.indexOf(
                                        String.valueOf(request.getFromBuilding()))) % 5 <= 2) {
                            flag1 = false;
                        } else if (String.valueOf(request.getFromBuilding()).equals(atBuilding) &
                                (buildNameList.indexOf(atBuilding) + 5 - buildNameList.indexOf(
                                        String.valueOf(request.getToBuilding()))) % 5 <= 2) {
                            flag1 = false;
                        }
                    }
                }
                if (flag1) {
                    direction = 1;
                }
            }
        }
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
