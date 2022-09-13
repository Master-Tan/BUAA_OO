import java.util.Scanner;

public class InputFactory {
    private Scanner sc;

    InputFactory() {
        sc = new Scanner(System.in);
    }

    boolean hasNextOperation() {
        return sc.hasNextLine();
    }

    String getNewOperation() {
        return sc.nextLine();
    }
}