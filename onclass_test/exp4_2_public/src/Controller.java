import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Controller { //控制器的单例模式
    private static final Controller CONTROLLER = new Controller();
    private Map<WorkingStage, WorkingList> workingLists;
    private boolean endTag;

    public static Controller getInstance() {
        return CONTROLLER;
    }

    public void initial() {
        workingLists = new HashMap<>();
        endTag = false;
        List<Worker> workerList = new ArrayList<>();
        int workerId = 1;
        for (WorkingStage workingStage : WorkingStage.values()) { //每种工序增加一个对应技能的 worker，并配备对应的队列
            WorkingList list = new WorkingList();
            Worker worker = new Worker(workerId, list, workingStage);// 将 worker 和 list 绑定
            workingLists.put(workingStage, list); // 将 stage 和 list 绑定
            workerList.add(worker);
            ++workerId;
        }
        for (Worker worker: workerList) {
            Thread thread = new Thread(worker);
            thread.start();
        }
    }

    public void addRequest(Request request) { //增添新的请求，并唤醒所有等待线程
        BitSet unfinishedStages = request.getUnfinishedStages();
        for (WorkingStage workingStage : WorkingStage.values()) {
            BitSet stages = (BitSet) unfinishedStages.clone();
            stages.and(workingStage.getMask()); // TODO(6)
            if (!stages.isEmpty()) {
                WorkingList list = workingLists.get(workingStage);
                list.addRequest(request);
                break;
            }
        }
    }

    public synchronized void setEndTag() { //标记所有任务完成，唤醒所有线程
        endTag = true;
        notifyAllWorkers();
    }

    public synchronized boolean getEndTag() {
        return endTag;
    }

    private void notifyAllWorkers() {
        for (WorkingStage workingStage : WorkingStage.values()) {
            WorkingList list = workingLists.get(workingStage);
            synchronized (list) {
                list.notifyAll();
            }
        }
    }
}
