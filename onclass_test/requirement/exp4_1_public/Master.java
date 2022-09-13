import java.util.ArrayList;
import java.util.List;

public class Master implements Runnable{
    private final TaskList taskList;
    private final List<Slave> slaves;
    private boolean allReceived;

    public Master() {
        this.taskList = TaskList.getSingleton();
        this.slaves = new ArrayList<>();
        this.allReceived = false;
    }

    private void initSlaves() {
        for (int i = 0; i < 5; i++) {
            Slave slave = new Slave(this, i);
            slaves.add(slave);
            new Thread(slave).start();
        }
    }

    public boolean masterFree() {
        return allReceived;
    }

    @Override
    public void run() {
        TaskInput taskInput = new TaskInput(System.in); // TaskInput类用于读取和处理输入
        initSlaves();
        while (true) {
            TaskRequest taskRequest = taskInput.nextRequest();
            if (taskRequest == null) {
                break;
            } else {
                taskList.addTask(taskRequest);
            }
        }
        this.allReceived = true;  // 标记Master线程结束了输入
        Printer.println("Master is free now");
    }
}
