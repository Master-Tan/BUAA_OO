public class Num extends Operator {
    private int value;
    public Num(int value) {
        super(null, null);
        this.value = value;
    }

    public int getResult() {
        return value;
    }
}
