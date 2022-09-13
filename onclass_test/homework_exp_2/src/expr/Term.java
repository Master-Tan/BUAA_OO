package expr;

import java.util.ArrayList;
import java.util.Iterator;

public class Term implements Factor {
    private final ArrayList<Factor> factors;

    public Term() {
        this.factors = new ArrayList<>();
    }

    public Term(Factor factor) {
        this.factors = new ArrayList<>();
        this.factors.add(factor);
    }

    public Term(ArrayList<Factor> factors) {
        this.factors = factors;
    }

    public void addFactor(Factor factor) {
        this.factors.add(factor);
    }

    public String toString() {
        Iterator<Factor> iter = factors.iterator();
        StringBuilder sb = new StringBuilder();

        assert iter.hasNext();
        sb.append(iter.next().toString());

        while (iter.hasNext()) {
            sb.append(" * ");
            sb.append(iter.next().toString());
        }
        return sb.toString();
    }

    @Override
    public Factor simplify() {
        assert factors.size() > 0;

        if (factors.size() == 1) {
            return factors.get(0).simplify();
        } else {
            ArrayList<Factor> newFactors = new ArrayList<>();
            for (Factor factor : factors) {
                newFactors.add(factor.simplify());
            }
            return new Term(newFactors);
        }
    }
}
