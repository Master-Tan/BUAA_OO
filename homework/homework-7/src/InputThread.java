import com.oocourse.elevator3.ElevatorInput;
import com.oocourse.elevator3.ElevatorRequest;
import com.oocourse.elevator3.PersonRequest;
import com.oocourse.elevator3.Request;

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
            Request request = elevatorInput.nextRequest();
            // when request == null
            // it means there are no more lines in stdin
            if (request == null) {
                break;
            } else {
                // a new valid request
                if (request instanceof PersonRequest) {

                    // a PersonRequest
                    // your code here
                    // 得到一个新的乘客请求，加入请求池中
                    controller.addPersonRequest(new MyRequest(request));

                    // System.out.println("A PersonRequest:    " + request);
                } else if (request instanceof ElevatorRequest) {
                    // an ElevatorRequest
                    // your code here
                    // 得到一个新的乘客请求，加入请求池中
                    controller.addElevatorRequest((ElevatorRequest) request);

                    // System.out.println("An ElevatorRequest: " + request);
                }
            }
        }

        controller.close();

        try {
            elevatorInput.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }
}
