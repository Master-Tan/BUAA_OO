public class Mul extends Operator {
    public Mul(Operator left, Operator right) {
        super(left, right);
    }

    public int getResult() {
        return getLeft().getResult() * getRight().getResult();
    }
}
