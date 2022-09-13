import java.util.ArrayList;

public interface DecisionMaker {
    void ask(Elevator elevator); // 获取请求池以及电梯当前信息并进行调度计算

    ArrayList<MyRequest> whoToPickUp(); // 返回当前计算所得需载的客人

    ArrayList<MyRequest> whoToPutDown(); // 返回当前楼层下楼的人

    int nextDirection(); // 返回是否需要调转方向
}
