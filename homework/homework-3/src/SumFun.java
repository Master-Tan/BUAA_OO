import java.math.BigInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SumFun {

    public SumFun() {
    }

    public static String substituteInto(String input) {

        StringBuilder sb = new StringBuilder();
        int length = input.length();

        for (int i = 0; i < length; i++) {

            Pattern sumPattern = Pattern.compile("^sum\\(");
            Matcher sumMatcher = sumPattern.matcher(input.substring(i));

            if (sumMatcher.find()) {
                sb.append("(");
                int pos = 1;
                int j;
                for (j = 4; pos != 0; j++) {
                    if (input.charAt(i + j) == '(') {
                        pos++;
                    }
                    if (input.charAt(i + j) == ')') {
                        pos--;
                    }
                }
                String[] sumArgs = input.substring(i + 4, i + j - 1).split(",");
                BigInteger begin = new BigInteger(sumArgs[1]);
                BigInteger end = new BigInteger(sumArgs[2]);
                if (begin.compareTo(end) > 0) {
                    sb.append("0");
                } else {
                    String str = "(" + sumArgs[3] + ")";
                    for (BigInteger k = begin; k.compareTo(end) <= 0;
                         k = k.add(new BigInteger("1"))) {
                        StringBuilder sb1 = new StringBuilder();
                        for (int g = 0; g < str.length(); g++) {
                            if (g == 0) {
                                if (str.charAt(g) == 'i') {
                                    sb1.append("(" + String.valueOf(k) + ")");
                                } else {
                                    sb1.append(str.charAt(g));
                                }
                            } else {
                                if (str.charAt(g) == 'i' & str.charAt(g - 1) != 's') {
                                    sb1.append("(" + String.valueOf(k) + ")");
                                } else {
                                    sb1.append(str.charAt(g));
                                }
                            }
                        }
                        sb.append(sb1.toString());
                        //  sb.append(str.replaceAll("i", "(" + String.valueOf(k) + ")"));
                        if (!k.equals(end)) {
                            sb.append("+");
                        }
                    }
                }
                i = i + j - 1;
                sb.append(")");
            } else {
                sb.append(input.charAt(i));
            }
            // System.out.println(sb.toString());
        }
        return sb.toString();
    }
}
