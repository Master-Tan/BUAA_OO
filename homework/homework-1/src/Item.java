import java.math.BigInteger;
import java.util.HashMap;
import java.util.Set;
import java.util.TreeSet;

public class Item {

    private HashMap<BigInteger, BigInteger> expression;
    private BigInteger maxIndex;

    public Item(String s) {
        expression = new HashMap<>();
        if (s.equals("x")) {
            expression.put(new BigInteger("1"), new BigInteger("1"));
            maxIndex = new BigInteger("1");
        }
        else if (s.equals("")) {
            maxIndex = new BigInteger("0");
        }
        else {
            expression.put(new BigInteger("0"), new BigInteger(s));
            maxIndex = new BigInteger("0");
        }
    }

    public Item pow(Item otherItem) {
        Item thisItem = new Item("1");
        BigInteger i = new BigInteger("0");
        for (; i.compareTo(otherItem.getExpression().get(new BigInteger("0"))) < 0;
             i = i.add(new BigInteger("1"))) {
            thisItem = thisItem.mul(this);
        }
        return thisItem;
    }

    public Item mul(Item otherItem) {
        Item thisItem = new Item("0");
        BigInteger i = new BigInteger("0");
        BigInteger thisMaxIndex;
        thisMaxIndex = this.maxIndex.add(otherItem.getMaxIndex());
        for (; i.compareTo(this.maxIndex) <= 0; i = i.add(new BigInteger("1"))) {
            BigInteger j = new BigInteger("0");
            for (; j.compareTo(otherItem.getMaxIndex()) <= 0; j = j.add(new BigInteger("1"))) {
                Item item = new Item("");
                if (this.expression.get(i) != null && otherItem.getExpression().get(j) != null) {
                    item.getExpression().put(i.add(j),
                            this.expression.get(i).multiply(otherItem.getExpression().get(j)));
                    item.setMaxIndex(i.add(j));
                    thisItem = thisItem.add(item);
                }
            }
        }
        thisItem.setMaxIndex(thisMaxIndex);
        return thisItem;
    }

    public Item sub(Item otherItem) {
        Item thisItem = new Item("");
        BigInteger i = new BigInteger("0");
        BigInteger thisMaxIndex;
        if (this.maxIndex.compareTo(otherItem.getMaxIndex()) < 0) {
            thisMaxIndex = otherItem.getMaxIndex();
        }
        else {
            thisMaxIndex = this.maxIndex;
        }
        for (; i.compareTo(thisMaxIndex) <= 0; i = i.add(new BigInteger("1"))) {
            if (this.expression.get(i) != null && otherItem.getExpression().get(i) != null) {
                thisItem.getExpression().put(i,
                        this.expression.get(i).subtract(otherItem.getExpression().get(i)));
            }
            else if (this.expression.get(i) != null) {
                thisItem.getExpression().put(i, this.expression.get(i));
            }
            else if (otherItem.getExpression().get(i) != null) {
                thisItem.getExpression().put(i,
                        otherItem.getExpression().get(i).multiply(new BigInteger("-1")));
            }
        }
        thisItem.setMaxIndex(thisMaxIndex);
        return thisItem;
    }

    public Item add(Item otherItem) {
        Item thisItem = new Item("");
        BigInteger i = new BigInteger("0");
        BigInteger thisMaxIndex;
        if (this.maxIndex.compareTo(otherItem.getMaxIndex()) < 0) {
            thisMaxIndex = otherItem.getMaxIndex();
        }
        else {
            thisMaxIndex = this.maxIndex;
        }
        for (; i.compareTo(thisMaxIndex) <= 0; i = i.add(new BigInteger("1"))) {
            if (this.expression.get(i) != null && otherItem.getExpression().get(i) != null) {
                thisItem.getExpression().put(i,
                        this.expression.get(i).add(otherItem.getExpression().get(i)));
            }
            else if (this.expression.get(i) != null) {
                thisItem.getExpression().put(i, this.expression.get(i));
            }
            else if (otherItem.getExpression().get(i) != null) {
                thisItem.getExpression().put(i, otherItem.getExpression().get(i));
            }
        }
        thisItem.setMaxIndex(thisMaxIndex);
        return thisItem;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        Set<BigInteger> set = expression.keySet();
        TreeSet<BigInteger> sortedSet = new TreeSet<>();
        sortedSet.addAll(set);
        TreeSet descendingSortedSet = (TreeSet) sortedSet.descendingSet();
        for (Object o : descendingSortedSet) {
            if (expression.get((BigInteger) o).compareTo(new BigInteger("0")) < 0) {
                continue;
            }
            if (!expression.get((BigInteger) o).toString().equals("0")) {
                if (o.toString().equals("0")) {
                    sb.append(expression.get((BigInteger) o).toString());
                }
                else if (o.toString().equals("1")) {
                    getUp1(sb, o);
                }
                else if (o.toString().equals("2")) {
                    getUp2(sb, o);
                }
                else {
                    getUp(sb, o);
                }
                expression.put((BigInteger) o, new BigInteger("0"));
                break;
            }
        }
        for (Object o : descendingSortedSet) {
            if (!expression.get((BigInteger) o).toString().equals("0")) {
                if (expression.get((BigInteger) o).toString().charAt(0) != '-') {
                    sb.append("+");
                }
                if (o.toString().equals("0")) {
                    sb.append(expression.get((BigInteger) o).toString());
                }
                else if (o.toString().equals("1")) {
                    getUp1(sb, o);
                }
                else if (o.toString().equals("2")) {
                    getUp2(sb, o);
                }
                else {
                    getUp(sb, o);
                }
            }
        }
        if (sb.toString().length() == 0) {
            return "0";
        }
        else {
            return sb.toString();
        }
    }

    private void getUp1(StringBuilder sb, Object o) {
        if (expression.get((BigInteger) o).toString().equals("-1")) {
            sb.append("-");
        }
        else if (!expression.get((BigInteger) o).toString().equals("1")) {
            sb.append(expression.get((BigInteger) o).toString() + "*");
        }
        sb.append("x");
    }

    private void getUp2(StringBuilder sb, Object o) {
        if (expression.get((BigInteger) o).toString().equals("-1")) {
            sb.append("-");
        }
        else if (!expression.get((BigInteger) o).toString().equals("1")) {
            sb.append(expression.get((BigInteger) o).toString() + "*");
        }
        sb.append("x" + "*" + "x");
    }

    private void getUp(StringBuilder sb, Object o) {
        if (expression.get((BigInteger) o).toString().equals("-1")) {
            sb.append("-");
        }
        else if (!expression.get((BigInteger) o).toString().equals("1")) {
            sb.append(expression.get((BigInteger) o).toString() + "*");
        }
        sb.append("x" + "**" + o.toString());
    }

    public BigInteger getMaxIndex() {
        return maxIndex;
    }

    public void setMaxIndex(BigInteger maxIndex) {
        this.maxIndex = maxIndex;
    }

    public HashMap<BigInteger, BigInteger> getExpression() {
        return expression;
    }

    public void setExpression(HashMap<BigInteger, BigInteger> expression) {
        this.expression = expression;
    }
}
