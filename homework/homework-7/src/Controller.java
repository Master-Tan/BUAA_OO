import com.oocourse.elevator3.ElevatorRequest;

import java.util.ArrayList;
import java.util.Arrays;

public class Controller {

    private RequestPool requestPool;

    private int min;

    public Controller() {

        // 创建一个请求池
        requestPool = new RequestPool();

        // 创建所有电梯线程并开始运行（处于可接客状态）
        ArrayList<String> buildNameList = new ArrayList<String>(
                Arrays.asList("A", "B", "C", "D", "E")); // 所有的楼号

        int id = 1;
        for (String buildName : buildNameList) {
            addBuildingElevator(buildName, id, 8, new Double(0.6 * 1000).longValue());
            id++;
        }
        addFloorElevator(1, 6, 8, new Double(0.6 * 1000).longValue(), 31);
        // TimableOutput.println("all elevator thread started");

    }

    private void addBuildingElevator(String buildName, int id, int capacity, long speed) {

        // 为每一个电梯创建一个决策者
        DecisionMaker decisionMaker = new LookBuildingDecisionMaker(
                buildName, requestPool); // Look算法

        Elevator elevator = new BuildingElevator(buildName, id, capacity, speed,
                requestPool, decisionMaker);

        ((BuildingElevator) elevator).start();

        // 向请求池中的电梯列表注册此电梯线程
        requestPool.addElevators(elevator);
    }

    private void addFloorElevator(int atFloor, int id, int capacity, long speed, int switchInfo) {

        // 为每一个电梯创建一个决策者
        DecisionMaker decisionMaker = new LookFloorDecisionMaker(
                atFloor, switchInfo, requestPool); // Look算法

        Elevator elevator = new FloorElevator(atFloor, id, capacity, speed, switchInfo,
                requestPool, decisionMaker);

        ((FloorElevator) elevator).start();

        // 向请求池中的电梯列表注册此电梯线程
        requestPool.addElevators(elevator);



    }

    public void addPersonRequest(MyRequest request) {

        requestPool.addPersonRequest(request);

    }

    public void addElevatorRequest(ElevatorRequest request) {
        if (request.getType().equals("building")) {
            addBuildingElevator(String.valueOf(request.getBuilding()), request.getElevatorId(),
                    request.getCapacity(), new Double(request.getSpeed() * 1000).longValue());
        } else {
            addFloorElevator(request.getFloor(), request.getElevatorId(), request.getCapacity(),
                    new Double(request.getSpeed() * 1000).longValue(), request.getSwitchInfo());
        }
        requestPool.addElevatorRequest();
    }

    public void close() {
        requestPool.close();
    }

}
