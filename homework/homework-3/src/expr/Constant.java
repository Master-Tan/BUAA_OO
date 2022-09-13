package expr;

//常量因子
public class Constant implements Factor {
    private final String num;

    public Constant(String num) {
        this.num = num;
    }

    public String toString() {
        return this.num;
    }
}
