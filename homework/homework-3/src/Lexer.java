import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Lexer {
    private final String input;
    private int pos = 0;
    private String curToken;
    private boolean isOperator;
    private int flag = 0;

    public Lexer(String input) {
        flag = 0;
        this.input = preProcess(input);
        // System.out.println(this.input);
        this.isOperator = true;
        this.next();
    }

    // 去除连续正负号
    private String preProcess(String input) {
        StringBuilder sb = new StringBuilder();
        int length = input.length();
        if (input.charAt(0) == '+' | input.charAt(0) == '-') {
            sb.append("0");
        }
        for (int i = 0; i < length; i++) {
            int opt = 1;
            if (input.charAt(i) == '+' | input.charAt(i) == '-') {
                while (i < length & (input.charAt(i) == '+' | input.charAt(i) == '-')) {
                    if (input.charAt(i) == '-') {
                        opt *= -1;
                    }
                    i++;
                }
                if (opt == 1) {
                    sb.append("+");
                }
                else {
                    sb.append("-");
                }
                i--;
            }
            else {
                sb.append(input.charAt(i));
            }
        }
        return prepreProcess(sb.toString());
    }

    // 去除"**+"
    private String prepreProcess(String str) {
        StringBuilder sb = new StringBuilder();
        int length = str.length();
        for (int i = 0; i < length; i++) {
            int opt = 1;
            if (str.charAt(i) == '*') {
                if (str.charAt(i + 1) == '*') {
                    if (str.charAt(i + 2) == '+') {
                        sb.append("**");
                        i += 2;
                        continue;
                    }
                }
            }
            sb.append(str.charAt(i));
        }
        return sb.toString();
    }

    // 获得一个带符号整数
    private String getConstant(String s) {
        StringBuilder sb = new StringBuilder();
        sb.append(s);
        while (pos < input.length() && Character.isDigit(input.charAt(pos))) {
            sb.append(input.charAt(pos));
            ++pos;
        }
        return sb.toString();
    }

    public void next() {
        if (pos == input.length()) {
            return;
        }
        //  处理单目负号
        if (flag == 1) {
            curToken = "*";
            ++pos;
            flag = 0;
            isOperator = false;
            return;
        }

        Pattern triPattern = Pattern.compile("^((sin\\()|(cos\\())");
        Matcher triMatcher = triPattern.matcher(input.substring(pos));

        char c = input.charAt(pos);
        if (Character.isDigit(c)) {
            curToken = this.getConstant("");
            isOperator = true;
        }
        else if (c == '+') {
            nextAdd(c);
        }
        else if (c == '-') {
            nextSub(c);
        }
        else if (c == '*') {
            ++pos;
            if (input.charAt(pos) == '*') {
                ++pos;
                curToken = "**";
                isOperator = false;
            }
            else {
                curToken = "*";
                isOperator = false;
            }
        }
        else if (triMatcher.find()) {
            curToken = triMatcher.group(0);
            pos += 4;
            isOperator = false;
        }
        else if (c == '(' | c == ')') {
            ++pos;
            curToken = String.valueOf(c);
            if (c == '(') {
                isOperator = false;
            }
            else {
                isOperator = true;
            }
        }
        // else if (c == 'x') {
        else {
            ++pos;
            curToken = String.valueOf(c);
            isOperator = true;
        }
        quiteZero();
    }

    private void nextSub(char c) {
        if (!isOperator) {
            curToken = "-1";
            flag = 1;
            isOperator = true;
        }
        else {
            ++pos;
            curToken = String.valueOf(c);
            isOperator = false;
        }
    }

    private void nextAdd(char c) {
        if (!isOperator) {
            curToken = "1";
            flag = 1;
            isOperator = true;
        }
        else {
            ++pos;
            curToken = String.valueOf(c);
            isOperator = false;
        }
    }

    private void quiteZero() {
        while (pos < input.length() && input.charAt(pos) == ' ') {
            ++pos;
        }
    }

    public String peek() {
        return this.curToken;
    }
}
