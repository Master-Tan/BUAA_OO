import com.oocourse.TimableOutput;

public class Main {
    public static void main(String[] args) {
        TimableOutput.initStartTimestamp();

        Master master = new Master();
        new Thread(master).start();
    }
}
