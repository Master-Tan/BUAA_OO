public class Request {
    private final int leaveTime;
    private final int backTime;
    private final String destination;

    public Request(int leaveTime, int backTime, String destination) {
        this.backTime = backTime;
        this.leaveTime = leaveTime;
        this.destination = destination;
    }

    public String getDestination() {
        return destination;
    }

    public int getLeaveTime() {
        return leaveTime;
    }

    public int getBackTime() {
        return backTime;
    }

    public String toString() {
        //TODO
        //请替换sentence为合适内容(3)
        return String.format("<destination:%s FROM-%d-TO-%d>", destination, leaveTime, backTime);
    }
}