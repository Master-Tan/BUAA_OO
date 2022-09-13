import expr.Expression;
import com.oocourse.spec2.ExprInput;
import com.oocourse.spec2.ExprInputMode;

import java.util.ArrayList;

public class MainClass {
    public static void main(String[] args) {
        // 实例化一个ExprInput类型的对象scanner
        // 由于是一般读入模式，所以我们实例化时传递的参数为ExprInputMode.NormalMode
        ExprInput scanner = new ExprInput(ExprInputMode.NormalMode);

        // 获取自定义函数个数
        int cnt = scanner.getCount();

        SelfDefineFun selfDefineFun = new SelfDefineFun();

        // 读入自定义函数
        for (int i = 0; i < cnt; i++) {
            String func = scanner.readLine();
            // 存储或者解析逻辑
            selfDefineFun.addFun(func.replaceAll(" ", "").replaceAll("\t", ""));
        }

        // 读入最后一行表达式
        String input = scanner.readLine().replaceAll(" ", "").replaceAll("\t", "");

        SumFun sumFun = new SumFun();

        // 求和函数以及自定义函数解析
        String substitutedInput = sumFun.substituteInto(
                selfDefineFun.substituteInto(input).replaceAll(" ", "").replaceAll("\t", ""))
                .replaceAll(" ", "").replaceAll("\t", "");

        //  System.out.println(substitutedInput);

        //  表达式括号展开相关的逻辑
        String expr = substitutedInput.replaceAll(" ", "").replaceAll("\t", "");

        //  System.out.println(expr);

        Lexer lexer = new Lexer(expr);
        Parser parser = new Parser(lexer);

        Expression expression = parser.parseExpression();
        //  System.out.println(expression);
        Item calculatedExpression = calculate(expression);
        //  System.out.println(calculatedExpression);
        TriSimplify triSimplify = new TriSimplify(calculatedExpression);
        Item simplifyExpression = triSimplify.simplify();
        System.out.println(simplifyExpression);

        //  System.out.println(new Item("x").add(
        //  new Item("1")).sub(new Item("2")).pow(new Item("5")).mul(new Item("10")));
        //    System.out.println(new Item("-1").sub(new Item("x")).mul(
        //    new Item("y")).pow(new Item("3")));
        // 表达式括号展开相关的逻辑
    }

    private static Item calculate(Expression expression) {
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
                } else if (expr.equals("-")) {
                    Item item = item1.sub(item2);
                    array.remove(item1);
                    array.remove(item2);
                    array.add(item);
                } else if (expr.equals("*")) {
                    Item item = item1.mul(item2);
                    array.remove(item1);
                    array.remove(item2);
                    array.add(item);
                } else {
                    Item item = item1.pow(item2);
                    array.remove(item1);
                    array.remove(item2);
                    array.add(item);
                }
            } else if (expr.equals("sin") | expr.equals("cos")) {
                Item item1 = array.get(array.size() - 1);
                if (expr.equals("sin")) {
                    Item item = item1.sin();
                    array.remove(item1);
                    array.add(item);
                } else {
                    Item item = item1.cos();
                    array.remove(item1);
                    array.add(item);
                }
            } else {
                Item item = new Item(expr);
                array.add(item);
            }
        }
        return array.get(0);
    }
}

