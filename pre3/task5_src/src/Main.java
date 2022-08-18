import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Main {
    public static void main(String[] args) {
        InputFactory in = new InputFactory();
        Map<Integer, Vehicle> idToVec = new HashMap<>(1000);
        while (in.hasNextOperation()) {
            String opStr = in.getNewOperation();
            List<String> ops = new ArrayList<>(Arrays.asList(opStr.split(" ")));

            // for create
            if ("create".equals(ops.get(0))) {
                int id = Integer.parseInt(ops.get(2));
                Vehicle vec = Factory.getNew(ops);
                idToVec.put(id, vec);
            }
            // for call
            else {
                int id = Integer.parseInt(ops.get(1));
                Vehicle vec = idToVec.get(id);
                switch (ops.get(2)) {
                    case "run":
                        vec.run();
                        break;
                    case "getPrice":
                        vec.getPrice();

                        break;
                    case "work":
                        if (vec instanceof Bus) {
                            ((Bus) vec).work();
                        } else if (vec instanceof Sprinkler) {
                            ((Sprinkler) vec).work();
                        }
                        break;
                    case "getIn":
                        ((Bus) vec).getIn(1);
                        break;
                    case "getOff":
                        ((Bus) vec).getOff();
                        break;
                    default:
                        break;
                }
            }
        }
    }
} 
