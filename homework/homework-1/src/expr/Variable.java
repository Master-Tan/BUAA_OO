package expr;

//变量因子
public class Variable implements Factor {
    private final String var;

    public Variable(String num) {
        this.var = num;
    }

    public String toString() {
        return this.var;
    }
}
