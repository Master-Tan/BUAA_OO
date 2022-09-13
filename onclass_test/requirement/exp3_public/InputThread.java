import main.java.com.oocourse.OutRequest;
import main.java.com.oocourse.StuRequest;

public class InputThread extends Thread {
    private final RequestQueue waitQueue;

    public InputThread(RequestQueue waitQueue) {
        this.waitQueue = waitQueue;
    }

    @Override
    public void run() {
        OutRequest outRequest = new OutRequest(System.in);
        while (true) {
            StuRequest stuRequest = outRequest.getNextRequest();
            //TODO
            //请替换sentence为合适内容(2)
            if (stuRequest == null) {
                waitQueue.setEnd(true);
                System.out.println("Input End");
                return;
            } else {
                Request request = new Request(stuRequest.getLeaveTime()
                        , stuRequest.getBackTime(), stuRequest.getDestination());
                waitQueue.addRequest(request);
            }
        }
    }
}