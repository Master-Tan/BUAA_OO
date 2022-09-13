public class Sub extends Operator {
    public Sub(Operator left, Operator right) {
        super(left, right);
    }

    public int getResult() {
        return getLeft().getResult() - getRight().getResult();
    }
}