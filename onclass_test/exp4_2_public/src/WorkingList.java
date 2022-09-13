import java.util.ArrayList;
import java.util.List;

public class WorkingList { //工序对应的队列
    private final List<Request> requestList;

    WorkingList() {
        requestList = new ArrayList<>();
    }

    public synchronized void addRequest(Request request) { //在队列中新增任务
        requestList.add(request);
        notifyAll();
    }

    public synchronized Request getRequest() { //从队列中取出一个任务返回给 worker
        Request request = null;
        while (!Controller.getInstance().getEndTag()) { // TODO(1)
            if (requestList.isEmpty()) {
                try {
                    wait();
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
            } else {
                request = requestList.get(0);
                requestList.remove(request); // TODO(2)
                break;
            }
        }
        return request;
    }
}
