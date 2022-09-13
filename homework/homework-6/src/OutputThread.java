import com.oocourse.TimableOutput;

public class OutputThread {

    public static synchronized long println(String msg) {
        long time;
        time = TimableOutput.println(msg);
        return time;
    }

}
