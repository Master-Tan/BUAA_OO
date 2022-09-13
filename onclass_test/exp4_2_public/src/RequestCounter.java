public class RequestCounter {
    private int count;
    private static final RequestCounter COUNTER = new RequestCounter();

    RequestCounter() {
        count = 0;
    }

    public static RequestCounter getInstance() {
        return COUNTER;
    }

    public synchronized void release() { //代表完成一个任务
        count += 1; // TODO(5)
        notifyAll();
    }

    public synchronized void acquire() { //检验一个任务的完成，如果没有已完成的任务，等待
        while (true) {
            if (count > 0) {
                count -= 1;
                break;
            } else {
                try {
                    wait();
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
            }
        }
    }
}
