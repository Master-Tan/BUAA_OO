package expr;

import java.util.ArrayList;
import java.util.Iterator;

public class Basic implements Factor {

    private final ArrayList<Factor> factories;

    public Basic() {
        this.factories = new ArrayList<>();
    }

    public void addFactor(Factor factor) {
        this.factories.add(factor);
    }

    public String toString() {
        Iterator<Factor> iter = factories.iterator();
        StringBuilder sb = new StringBuilder();
        sb.append(iter.next().toString());
        if (iter.hasNext()) {
            sb.append(" ");
            sb.append(iter.next().toString());
            sb.append(" **");
            while (iter.hasNext()) {
                sb.append(" ");
                sb.append(iter.next().toString());
                sb.append(" **");
            }
        }
        return sb.toString();
    }
}
