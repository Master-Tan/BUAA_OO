package expr;

public class Var implements Factor {
    public String toString() {
        return "x";
    }

    @Override
    public Factor simplify() {
        return this;
    }
}
