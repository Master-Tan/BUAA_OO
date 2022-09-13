import expr.Expr;
import expr.Factor;

import java.util.Scanner;

public class MainClass {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        String input = scanner.nextLine();

        Lexer lexer = new Lexer(input);
        Parser parser = new Parser(lexer);

        Factor expr = parser.parseExpr().simplify();

        if (expr instanceof Expr) {
            String exprStr = expr.toString();
            System.out.println(exprStr.substring(1, exprStr.length() - 1));
        } else {
            System.out.println(expr);
        }
    }
}
