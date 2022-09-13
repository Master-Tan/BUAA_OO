import expression.Expr;
import expression.Term;

import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MainClass {
    private static final String patternTerm = "[0-9]+(\\*[0-9]+)*";
    public static final Pattern re = Pattern.compile(patternTerm);

    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        String inputExpr = scanner.next();

        Matcher matcher = re.matcher(inputExpr);

        Expr expr = new Expr();
        while (matcher.find()) {
            String termStr = matcher.group(0);
            Term term = new Term(termStr);
            expr.addTerm(term);
        }

        System.out.println(expr.toString());
    }
}
