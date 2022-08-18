import com.oocourse.TimableOutput;

public class Printer {
    public synchronized static void println(String s) {
        TimableOutput.println(s);
    }
}
