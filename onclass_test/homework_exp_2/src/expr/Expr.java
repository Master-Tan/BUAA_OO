package expr;

import java.util.ArrayList;
import java.util.Iterator;

public class Expr implements Factor {
    private final ArrayList<Term> terms;

    public ArrayList<Term> getTerms() {
        return terms;
    }

    public Expr() {
        this.terms = new ArrayList<>();
    }

    public void addTerm(Term term) {
        this.terms.add(term);
    }

    public String toString() {
        Iterator<Term> iter = terms.iterator();
        StringBuilder sb = new StringBuilder();
        sb.append('(');

        assert iter.hasNext();
        sb.append(iter.next().toString());

        while (iter.hasNext()) {
            sb.append(" + ");
            sb.append(iter.next().toString());
        }
        sb.append(')');
        return sb.toString();
    }

    @Override
    public Factor simplify() {
        assert terms.size() > 0;

        if (terms.size() == 1) {
            return terms.get(0).simplify();
        } else {
            Expr simpExpr = new Expr();
            for (Term term : terms) {
                // 化简 terms 中的每一项
                Factor factor = term.simplify();

                if (factor instanceof Term) {
                    simpExpr.addTerm((Term) factor);
                } else if (factor instanceof Expr) {
                    // (a + b) + c => a + b + c
                    // 提取嵌套表达式内部的每一项

                    Expr expr = (Expr) factor;
                    for (Term insideTerm : expr.getTerms()) {
                        simpExpr.addTerm(insideTerm);
                    }
                } else {
                    simpExpr.addTerm(new Term(factor));
                }
            }
            return simpExpr;
        }
    }
}
