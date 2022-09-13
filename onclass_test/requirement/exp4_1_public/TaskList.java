import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class TaskList {
    private volatile static TaskList singleton;
    private final List<TaskRequest> list;
    private final Lock lock;
    private final int SLAVE_NUM = 5;

    private TaskList() {
        this.list = new ArrayList<>();
        this.lock = new ReentrantLock();
    }

    public static TaskList getSingleton() {
        if (singleton == null) {
            synchronized (TaskList.class) {
                if (singleton == null) {
                    singleton = new TaskList();
                }
            }
        }
        return singleton;
    }

    public void addTask(TaskRequest task) { // 往列表中添加任务
        lock.lock();
        try{
            list.add(task);
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            lock.unlock();
        }
    }

    public TaskRequest fetchTask(int id) { // 获取任务，获取逻辑是根据id，如id为1，6，11，21的任务分配给id为1的Slave线程
        lock.lock();
        try {
            for (int i = 0; i < list.size(); i++) {
                if (!list.get(i).isDone() && list.get(i).getId() % SLAVE_NUM == id) {  // TODO(5)
                    return list.get(i);
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            lock.unlock();
        }
        return null;
    }
}
