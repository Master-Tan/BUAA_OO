import expr.Expression;
import com.oocourse.spec1.ExprInput;
import com.oocourse.spec1.ExprInputMode;

import java.util.ArrayList;

public class MainClass {
    public static void main(String[] args) {
        // 实例化一个ExprInput类型的对象scanner
        // 由于是一般读入模式，所以我们实例化时传递的参数为ExprInputMode.NormalMode
        ExprInput scanner = new ExprInput(ExprInputMode.NormalMode);

        // 一般读入模式下，读入一行字符串时使用readLine()方法，在这里我们使用其读入表达式
        String input = scanner.readLine();
        String expr = input.replaceAll(" ", "").replaceAll("\t","");
        Lexer lexer = new Lexer(expr);
        Parser parser = new Parser(lexer);

        Expression expression = parser.parseExpression();
        //  System.out.println(expression);
        Item simplifyExpression = simplify(expression);
        System.out.println(simplifyExpression);

        //  System.out.println(new Item("x").add(
        //  new Item("1")).sub(new Item("2")).pow(new Item("5")).mul(new Item("10")));
        // 表达式括号展开相关的逻辑
    }

    private static Item simplify(Expression expression) {
        String[] exprs = expression.toString().split(" ");
        ArrayList<Item> array = new ArrayList<>();
        int flag = 0;
        for (String expr : exprs) {
            if (flag == 0) {
                array.add(new Item(expr));
                flag = 1;
                continue;
            }
            if (expr.equals("+") | expr.equals("-") | expr.equals("*") | expr.equals("**")) {
                Item item1 = array.get(array.size() - 2);
                Item item2 = array.get(array.size() - 1);
                if (expr.equals("+")) {
                    Item item = item1.add(item2);
                    array.remove(item1);
                    array.remove(item2);
                    array.add(item);
                }
                else if (expr.equals("-")) {
                    Item item = item1.sub(item2);
                    array.remove(item1);
                    array.remove(item2);
                    array.add(item);
                }
                else if (expr.equals("*")) {
                    Item item = item1.mul(item2);
                    array.remove(item1);
                    array.remove(item2);
                    array.add(item);
                }
                else {
                    Item item = item1.pow(item2);
                    array.remove(item1);
                    array.remove(item2);
                    array.add(item);
                }
            }
            else {
                Item item = new Item(expr);
                array.add(item);
            }
        }
        return array.get(0);
    }
}

