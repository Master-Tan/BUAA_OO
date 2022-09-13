import com.oocourse.TimableOutput;

public class Printer {
    public static synchronized void println(String s) { //封装输出
        TimableOutput.println(s);
    }
}
