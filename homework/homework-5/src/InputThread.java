import com.oocourse.elevator1.ElevatorInput;
import com.oocourse.elevator1.PersonRequest;

import java.io.IOException;

public class InputThread extends Thread {

    private Controller controller;

    public InputThread(Controller controller) {
        this.controller = controller;
    }

    @Override
    public void run() {
        ElevatorInput elevatorInput = new ElevatorInput(System.in);
        while (true) {
            PersonRequest request = elevatorInput.nextPersonRequest();
            // when request == null
            // it means there are no more lines in stdin
            if (request == null) {
                break;
            } else {
                // 得到一个新的请求，加入请求池中
                controller.addRequest(request);
            }
        }

        controller.close();

        //  close the elevatorInput in the end
        try {
            elevatorInput.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
