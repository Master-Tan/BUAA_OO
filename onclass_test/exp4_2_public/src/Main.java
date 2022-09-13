import com.oocourse.TimableOutput;
import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        TimableOutput.initStartTimestamp(); //初始化时间戳
        Controller.getInstance().initial();
        Scanner scanner = new Scanner(System.in);
        int requestNum = 0;
        while (scanner.hasNext()) {
            String rawRequest = scanner.next();
            MyParser parser = new MyParser(rawRequest);
            Request request = new Request(parser.getRequestCode(),
                    parser.getWorkingStages(), parser.getPipelineLength());
            Controller.getInstance().addRequest(request);
            ++requestNum;
        }
        for (int i = 0; i < requestNum; ++i) { //查收所有的任务
            RequestCounter.getInstance().acquire();
        }
        Controller.getInstance().setEndTag(); //标记所有任务完成
    }
}
