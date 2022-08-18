import java.util.ArrayList;

public class MainClass {
    public static void main(String[] args) {
        RequestQueue waitQueue = new RequestQueue();

        ArrayList<RequestQueue> processingQueues = new ArrayList<>();
        //TODO
        //请将n替换成具体的数字(1)
        for (int i = 0; i < 3; i++) {
            RequestQueue parallelQueue = new RequestQueue();
            processingQueues.add(parallelQueue);
            Process process = new Process(parallelQueue, i);
            process.start();
        }

        Schedule schedule = new Schedule(waitQueue, processingQueues);
        schedule.start();

        InputThread inputThread = new InputThread(waitQueue);
        inputThread.start();
    }
}
