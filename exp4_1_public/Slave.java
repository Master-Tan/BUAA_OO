import java.sql.Date;
import java.util.ArrayList;
import java.util.List;


public class Slave implements Runnable{
    private final List<TaskRequest> tasks;
    private final int id;
    private final Master master;
    private boolean workDone;
    private final TaskList publicList;

    public Slave(Master master, int id) {
        this.tasks = new ArrayList<>();
        this.id = id;
        this.master = master;
        this.workDone = false;
        this.publicList = TaskList.getSingleton();
    }

    private boolean isFree() {
        return tasks.isEmpty();
    }

    private void settleTask(TaskRequest taskRequest) {
         taskRequest.setDone(true);// TODO(1)
    }

    private boolean hasWork() {
        return publicList.fetchTask(id) != null;
    }

    @Override
    public void run() {
        while(true) {
            if (isFree() && master.masterFree() && !hasWork()) {
                break;
            }
            if (hasWork()) {  // TODO(2)
                TaskRequest taskRequest = publicList.fetchTask(id);
                Printer.println(String.format("Slave %d fetches task %d", this.id, taskRequest.getId()));
                try {
                    Thread.sleep(new Double(taskRequest.getTime()).longValue());  // TODO(3)
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
                settleTask(taskRequest);  // TODO(4)
                Printer.println(String.format("Slave %d settles task %d", this.id, taskRequest.getId()));
            } else {
                try {
                    Thread.sleep(1000L);
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
            }
        }
        Printer.println(String.format("Slave %d is free now", this.id));
    }
}
