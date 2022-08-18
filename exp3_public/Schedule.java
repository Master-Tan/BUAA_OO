import java.util.ArrayList;

public class Schedule extends Thread {
    private final RequestQueue waitQueue;
    private final ArrayList<RequestQueue> processingQueues;

    public Schedule(RequestQueue waitQueue
            , ArrayList<RequestQueue> processingQueues) {
        this.waitQueue = waitQueue;
        this.processingQueues = processingQueues;
    }

    @Override
    public void run() {
        while (true) {
            //TODO
            //请替换sentence1为合适内容(7)
            if (waitQueue.isEmpty() && waitQueue.isEnd()) {
                for (int i = 0; i < processingQueues.size(); i++) {
                    processingQueues.get(i).setEnd(true);
                }
                System.out.println("Schedule End");
                return;
            }
            //TODO
            //请替换sentence2为合适内容(8)
            Request request = waitQueue.getOneRequest();
            if (request == null) continue;
            //TODO
            //请替换sentence3为合适内容(9)
            if (request.getDestination().equals("Beijing")) {
                processingQueues.get(0).addRequest(request);
            } else if (request.getDestination().equals("Domestic")) {
                processingQueues.get(1).addRequest(request);
            } else {
                processingQueues.get(2).addRequest(request);
            }
        }
    }
}


