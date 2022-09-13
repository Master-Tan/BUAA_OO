import expr.Expr;
import expr.Factor;
import expr.Number;
import expr.Power;
import expr.Term;
import expr.Var;

import java.math.BigInteger;

public class Parser {
    private final Lexer lexer;

    public Parser(Lexer lexer) {
        this.lexer = lexer;
    }

    public Expr parseExpr() {
        Expr expr = new Expr();
        expr.addTerm(parseTerm());

        while (lexer.peek().equals("+")) {
            lexer.next();
            expr.addTerm(parseTerm());
        }
        return expr;
    }

    public Term parseTerm() {
        Term term = new Term();
        term.addFactor(parseFactor());
        while (lexer.peek().equals("*")) {
            lexer.next();
            term.addFactor(parseFactor());
        }
        return term;
    }

    public Factor parseFactor() {
        if (lexer.peek().equals("(")) {
            lexer.next();
            Factor expr = parseExpr();
            lexer.next();
            if (lexer.peek().equals("**")) {
                lexer.next();
                return new Power(expr, parseNumber());
            }
            return expr;
        } else if (lexer.peek().equals("x")) {
            lexer.next();
            if (lexer.peek().equals("**")) {
                lexer.next();
                return new Power(new Var(), parseNumber());
            } else {
                return new Var();
            }
        } else {
            return parseNumber();
        }
    }

    public Number parseNumber() {
        BigInteger num = new BigInteger(lexer.peek());
        lexer.next();
        return new Number(num);
    }
}
