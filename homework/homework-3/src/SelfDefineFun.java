import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SelfDefineFun {

    private HashMap<String, ArrayList<String>> functions;

    public SelfDefineFun() {
        functions = new HashMap<>();
    }

    public void addFun(String str) {
        String funName = String.valueOf(str.charAt(0));
        ArrayList<String> args = new ArrayList<>();
        Pattern pattern = Pattern.compile("^\\(.*?\\)");
        Matcher matcher = pattern.matcher(str.substring(1));
        if (matcher.find()) {
            String string = matcher.group(0);
            String[] idVar = string.substring(1, string.length() - 1).split(",");
            args.addAll(Arrays.asList(idVar));
        }
        Pattern pattern1 = Pattern.compile("[=].*$");
        Matcher matcher1 = pattern1.matcher(str);
        if (matcher1.find()) {
            args.add("(" + matcher1.group(0).substring(1) + ")");
        }
        //  System.out.println("<" + funName + "," + args + ">");
        functions.put(funName, args);

    }

    public String substituteInto(String input) {
        StringBuilder sb = new StringBuilder();
        int length = input.length();

        for (int i = 0; i < length; i++) {
            String c = String.valueOf(input.charAt(i));
            if (functions.containsKey(c)) {
                int pos = 1;
                int j;
                for (j = 2; pos != 0; j++) {
                    if (input.charAt(i + j) == '(') {
                        pos++;
                    }
                    if (input.charAt(i + j) == ')') {
                        pos--;
                    }
                }

                String text = check(input, i, j);

                String[] args = text.split(",");
                StringBuilder sb1 = new StringBuilder();
                sb1.append(functions.get(c).get(functions.get(c).size() - 1));
                for (int k = 0; k < args.length; k++) {
                    if (functions.get(c).get(k).equals("x")) {
                        String str = sb1.toString();
                        StringBuilder sb2 = new StringBuilder();
                        sb2.append(str.replaceAll(functions.get(c).get(k), "(" + args[k] + ")"));
                        sb1 = sb2;
                    }
                }
                for (int k = 0; k < args.length; k++) {
                    if (!functions.get(c).get(k).equals("x")) {
                        String str = sb1.toString();
                        StringBuilder sb2 = new StringBuilder();
                        sb2.append(str.replaceAll(functions.get(c).get(k), "(" + args[k] + ")"));
                        sb1 = sb2;
                    }
                }
                sb.append(sb1.toString());
                i = i + j - 1;
            } else {
                sb.append(c);
            }
            //            System.out.println(sb.toString());
        }
        StringBuilder sb2 = new StringBuilder();
        for (String s : this.functions.keySet()) {
            sb2.append(s);
        }
        if (sb2.length() >= 1) {
            Pattern selfDefinePattern = Pattern.compile("[" + sb2.toString() + "]");
            Matcher selfDefineMatcher = selfDefinePattern.matcher(sb.toString());
            if (selfDefineMatcher.find()) {
                return (this.substituteInto(sb.toString()));
            }
        }
        return sb.toString();
    }

    private String check(String input, int i, int j) {
        String text = input.substring(i + 2, i + j - 1);
        if (text.contains("sum")) {
            text = SumFun.substituteInto(text);
        } else {
            int flag = 0;
            for (String s : this.functions.keySet()) {
                if (text.contains(s)) {
                    flag = 1;
                }
            }
            if (flag == 1) {
                text = this.substituteInto(text);
            }
        }
        //  System.out.println(text);
        return text;
    }

}
