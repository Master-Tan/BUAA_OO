public abstract class Vehicle {
    private int id;
    private int price;

    Vehicle(int id, int price) {
        this.id = id;
        this.price = price;
    }

    public abstract void run();
    
    public int getPrice() {
        return price;
    }
}