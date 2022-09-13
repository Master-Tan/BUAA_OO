import java.util.ArrayList;

public class RequestQueue {
    private ArrayList<Request> requests;
    private boolean isEnd;

    public RequestQueue() {
        requests = new ArrayList<>();
        this.isEnd = false;
    }

    public synchronized void addRequest(Request request) {
        requests.add(request);
        //TODO
        //请替换sentence1为合适内容(4)
        notifyAll();
    }

    public synchronized Request getOneRequest() {
        //TODO
        //请替换sentence2为合适内容(5)
        //请替换sentence3为合适内容(6)
        if (requests.isEmpty() & !isEnd) {
            try {
                this.wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        if (requests.isEmpty()) {
            return null;
        }
        Request request = requests.get(0);
        requests.remove(0);
        notifyAll();
        return request;
    }

    public synchronized void setEnd(boolean isEnd) {
        this.isEnd = isEnd;
        notifyAll();
    }

    public synchronized boolean isEnd() {
        notifyAll();
        return isEnd;
    }

    public synchronized boolean isEmpty() {
        notifyAll();
        return requests.isEmpty();
    }
}
