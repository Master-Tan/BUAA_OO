import com.oocourse.elevator1.PersonRequest;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

public class Controller {

    private RequestPool requestPool;
    private HashMap<String, DecisionMaker> decisionMakers;
    private HashMap<String, Elevator> elevators;

    public Controller() {

        // 创建一个请求池
        requestPool = new RequestPool();

        // 创建所有电梯线程并开始运行（处于可接客状态）
        ArrayList<String> buildNameList = new ArrayList<String>(
                Arrays.asList("A", "B", "C", "D", "E")); // 所有的楼号

        decisionMakers = new HashMap<>();
        elevators = new HashMap<>();
        int id = 1;
        for (String buildName : buildNameList) {
            addElevator(buildName, id);
            id++;
        }
        // TimableOutput.println("all elevator thread started");
    }

    private void addElevator(String buildName, int id) {

        // 为每一个电梯创建一个决策者
        DecisionMaker decisionMaker = new LookDecisionMaker(buildName, id, requestPool); // Look算法
        // DecisionMaker DecisionMaker decisionMaker = new NoneDecisionMaker(requestPool); // None算法

        Elevator elevator = new Elevator(buildName, id, requestPool, decisionMaker);

        decisionMakers.put(buildName, decisionMaker);
        elevator.start();
        elevators.put(buildName, elevator);

        // 向请求池中的空等列表注册此电梯线程
        requestPool.getElevator().put(elevator, false);
    }

    public void addRequest(PersonRequest request) {
        requestPool.addRequest(request);
    }

    public void close() {
        requestPool.close();
    }
}
