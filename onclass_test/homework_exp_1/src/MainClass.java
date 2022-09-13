import java.util.HashMap;
import java.util.Scanner;

public class MainClass {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        HashMap<String, Integer> parameters = new HashMap<>();
        int n = scanner.nextInt();
        // get values of parameters
        for (int i = 0; i < n; i++) {
            parameters.put(scanner.next(), scanner.nextInt());
        }
        scanner.nextLine();
        String expression = scanner.nextLine(); // get Expression
        Parser parser = new Parser(parameters);
        System.out.println(parser.parse(expression.replaceAll("[ \t]", "")).getResult());
    }
}