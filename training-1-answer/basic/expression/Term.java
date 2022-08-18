package expression;

import java.util.ArrayList;

public class Term {
    private ArrayList<Integer> factors;

    public Term(String s) {
        factors = new ArrayList<>();
        String[] factorStrs = s.split("\\*");
        for (String factorStr : factorStrs) {
            factors.add(Integer.parseInt(factorStr));
        }
    }

    @Override
    public String toString() {
        if (factors.size() == 1) {
            return factors.get(0).toString();
        } else {
            StringBuilder sb = new StringBuilder();
            sb.append(factors.get(0));
            sb.append(" ");
            sb.append(factors.get(1));
            sb.append(" ");
            sb.append("*");
            for (int i = 2; i < factors.size(); i++) {
                sb.append(" ");
                sb.append(factors.get(i));
                sb.append(" ");
                sb.append("*");
            }
            return sb.toString();
        }
    }
}
