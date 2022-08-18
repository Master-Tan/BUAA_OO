public class Lexer {
    private final String input;
    private int pos = 0;
    private String curToken;

    public Lexer(String input) {
        this.input = input;
        this.next();
    }

    private String getNumber() {
        StringBuilder sb = new StringBuilder();
        while (pos < input.length() && Character.isDigit(input.charAt(pos))) {
            sb.append(input.charAt(pos));
            ++pos;
        }

        return sb.toString();
    }

    public void next() {
        while (pos < input.length() && " \t".indexOf(input.charAt(pos)) != -1) {
            ++pos;
        }

        if (pos >= input.length()) {
            return;
        }

        char c = input.charAt(pos);
        if (Character.isDigit(c)) {
            curToken = getNumber();
        } else if (c == '*' && pos < input.length() - 1 && input.charAt(pos + 1) == '*') {
            pos += 2;
            curToken = "**";
        } else if ("()+*x".indexOf(c) != -1) {
            pos += 1;
            curToken = String.valueOf(c);
        }
    }

    public String peek() {
        return this.curToken;
    }
}
