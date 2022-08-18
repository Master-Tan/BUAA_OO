public class Bus extends Vehicle implements Manned, Engineered {
    private int volume;
    private int passenger;

    public Bus(int id, int price, int volume) {
        super(id, price);
        this.volume = volume;
    }

    @Override
    public void run() {
        System.out.println("Wow, I can Run all day!");
    }

    @Override
    public void work() {
        System.out.println("Working!" + " " + this.volume + "L diesel oil used!");
    }

    @Override
    public void getIn(int newPassenger) {
        passenger = passenger + newPassenger;
        System.out.println("Wow! We have a new passenger!");
    }

    @Override
    public void getOff() {
        if (passenger <= 0) {
            System.out.println("Wow! Only Driver!");
        } else {
            passenger = passenger - 1;
            System.out.println("Wow! A passenger arrived at his or her destination!");
        }
    }
}
