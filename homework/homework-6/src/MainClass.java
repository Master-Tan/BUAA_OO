import com.oocourse.TimableOutput;

public class MainClass {
    public static void main(String[] args) throws Exception {

        // 初始化时间戳
        TimableOutput.initStartTimestamp();

        // 创建一个控制器
        Controller controller = new Controller();

        // 创建输入线程并开始运行（程序开始接受读入）
        Thread inputThread = new InputThread(controller);
        inputThread.start();

        // 关闭所有线程，程序结束
        // TimableOutput.println("Running… ");

    }
}