package expr;

import java.util.HashSet;
import java.util.Iterator;

public class Term {
    private final HashSet<Factor> factors;

    public Term() {
        this.factors = new HashSet<>();
    }

    public void addFactor(Factor factor) {
        this.factors.add(factor);
    }

    public String toString() {
        Iterator<Factor> iter = factors.iterator();
        StringBuilder sb = new StringBuilder();
        sb.append(iter.next().toString());
        if (iter.hasNext()) {
            sb.append(" ");
            sb.append(iter.next().toString());
            sb.append(" *");
            while (iter.hasNext()) {
                sb.append(" ");
                sb.append(iter.next().toString());
                sb.append(" *");
            }
        }
        return sb.toString();
    }
}
