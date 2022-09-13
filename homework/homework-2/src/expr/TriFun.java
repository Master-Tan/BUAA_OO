package expr;

public class TriFun implements Factor {

    private Expression expression;

    private String triSymbol;

    public TriFun(String triSymbol) {
        this.expression = new Expression();
        this.triSymbol = triSymbol;
    }

    public void addExpression(Expression expression) {
        this.expression = expression;
    }

    public String toString() {
        return expression.toString() + " " + triSymbol.substring(0, triSymbol.length() - 1);
    }

}
