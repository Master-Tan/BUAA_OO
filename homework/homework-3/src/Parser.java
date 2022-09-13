import expr.Basic;
import expr.Expression;
import expr.Factor;
import expr.Term;
import expr.TriFun;
import expr.Variable;
import expr.Constant;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Parser {
    private final Lexer lexer;

    public Parser(Lexer lexer) {
        this.lexer = lexer;
    }

    public TriFun parseTriFun(String triSymbol) {
        TriFun triFun = new TriFun(triSymbol);
        lexer.next();
        triFun.addExpression(parseExpression());
        return triFun;
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
        Pattern numPattern = Pattern.compile("^\\d*$");
        Matcher numMatcher = numPattern.matcher(lexer.peek());

        if (lexer.peek().equals("sin(") | lexer.peek().equals("cos(")) {
            Factor triFun = parseTriFun(lexer.peek());
            lexer.next();
            return triFun;
        }
        else if (lexer.peek().equals("(")) {
            lexer.next();
            Factor expression = parseExpression();
            lexer.next();
            return expression;
        }
        else if (numMatcher.find()) {
            String num = lexer.peek();
            lexer.next();
            return new Constant(num);
        }
        // else if (lexer.peek().equals("x")) {
        else {
            String var = lexer.peek();
            lexer.next();
            return new Variable(var);
        }
    }
}
