package expression;

import java.util.ArrayList;

public class Expr {
    private ArrayList<Term> terms = new ArrayList<>();

    public void addTerm(Term term) {
        terms.add(term);
    }

    @Override
    public String toString() {
        if (terms.size() == 1) {
            return terms.get(0).toString();
        } else {
            StringBuilder sb = new StringBuilder();
            sb.append(terms.get(0));
            sb.append(" ");
            sb.append(terms.get(1));
            sb.append(" ");
            sb.append("+");
            for (int i = 2; i < terms.size(); i++) {
                sb.append(" ");
                sb.append(terms.get(i));
                sb.append(" ");
                sb.append("+");
            }
            return sb.toString();
        }
    }
}
