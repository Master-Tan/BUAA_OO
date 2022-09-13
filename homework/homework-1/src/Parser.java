import expr.Basic;
import expr.Expression;
import expr.Factor;
import expr.Term;
import expr.Variable;
import expr.Constant;

public class Parser {
    private final Lexer lexer;

    public Parser(Lexer lexer) {
        this.lexer = lexer;
    }

    public Expression parseExpression() {
        Expression expression = new Expression();
        expression.addTerm(parseTerm());

        while (lexer.peek().equals("+") | lexer.peek().equals("-")) {
            expression.getOperators().add(lexer.peek());
            // System.out.println(expression.getOperators());
            lexer.next();
            expression.addTerm(parseTerm());
        }
        return expression;
    }

    public Term parseTerm() {
        Term term = new Term();
        term.addBasic(parseBasic());

        while (lexer.peek().equals("*")) {
            lexer.next();
            term.addBasic(parseBasic());
        }
        return term;
    }

    public Basic parseBasic() {
        Basic basic = new Basic();
        basic.addFactor(parseFactor());

        while (lexer.peek().equals("**")) {
            lexer.next();
            basic.addFactor(parseFactor());
        }
        return basic;
    }

    public Factor parseFactor() {
        if (lexer.peek().equals("(")) {
            lexer.next();
            Factor expression = parseExpression();
            lexer.next();
            return expression;
        } else {
            if (lexer.peek().equals("x")) {
                String var = lexer.peek();
                lexer.next();
                return new Variable(var);
            }
            else {
                String num = lexer.peek();
                lexer.next();
                return new Constant(num);
            }
        }
    }
}
