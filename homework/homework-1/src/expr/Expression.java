package expr;

import java.util.ArrayList;
import java.util.Iterator;

public class Expression implements Factor {
    private final ArrayList<Term> terms;

    private ArrayList<String> operators;

    private int flag = 0;

    public Expression() {
        this.terms = new ArrayList<>();
        this.operators = new ArrayList<>();
    }

    public void addTerm(Term term) {
        this.terms.add(term);
    }

    public String toString() {
        Iterator<Term> iter = terms.iterator();
        StringBuilder sb = new StringBuilder();
        sb.append(iter.next().toString());
        if (iter.hasNext()) {
            sb.append(" ");
            sb.append(iter.next().toString());
            String operator = operators.get(flag++);
            sb.append(" " + operator);
            while (iter.hasNext()) {
                sb.append(" ");
                sb.append(iter.next().toString());
                String operator1 = operators.get(flag++);
                sb.append(" " + operator1);
            }
        }
        flag = 0;
        return sb.toString();
    }

    public ArrayList<String> getOperators() {
        return operators;
    }

    public void setOperators(ArrayList<String> operators) {
        this.operators = operators;
    }
}
