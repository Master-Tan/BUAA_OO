import java.util.List;

public class Factory {
    public static Vehicle getNew(List<String> ops) {
        String type = ops.get(1);
        Integer id = Integer.parseInt(ops.get(2));
        Integer price = Integer.parseInt(ops.get(3));
        if ("Car".equals(type)) {
            Integer maxSpeed = Integer.parseInt(ops.get(4));
            Car car = new Car(id, price, maxSpeed);
            return car;
        } else if ("Sprinkler".equals(type)) {
            Integer volume = Integer.parseInt(ops.get(4));
            Sprinkler sprinkler = new Sprinkler(id, price, volume);
            return sprinkler;
        } else {
            Integer volume = Integer.parseInt(ops.get(4));
            Bus bus = new Bus(id, price, volume);
            return bus;
        }
    }
}
