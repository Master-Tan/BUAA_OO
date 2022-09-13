package expr;

public class Power implements Factor {
    private final Factor base;
    private final Number exp;

    public Power(Factor base, Number exp) {
        this.base = base;
        this.exp = exp;
    }

    @Override
    public String toString() {
        return base + "**" + exp;
    }

    @Override
    public Factor simplify() {
        return new Power(base.simplify(), exp);
    }
}
