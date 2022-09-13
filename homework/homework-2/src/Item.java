import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Item {

    // HashMap<HashMap<指数名, 指数值>, 系数值> expression；
    private HashMap<HashMap<String, BigInteger>, BigInteger> expression;

    public Item(String s) {
        expression = new HashMap<>();
        Pattern numPattern = Pattern.compile("^([+]|[-])?\\d*$");
        Matcher numMatcher = numPattern.matcher(s);
        if (!s.equals("")) {
            if (numMatcher.find()) {
                //                if (!s.equals("0")) {
                HashMap<String, BigInteger> index = new HashMap<>();
                index.put("x", new BigInteger("0"));
                expression.put(index, new BigInteger(s));
                //                }
            } else {
                HashMap<String, BigInteger> index = new HashMap<>();
                index.put(s, new BigInteger("1"));
                expression.put(index, new BigInteger("1"));
            }
        }
    }

    public Item sin() {
        if (this.toString().equals("0")) {
            return new Item("0");
        }
        if (this.toString1().charAt(0) == '-') {
            return (new Item("sin(" + this.mul(new Item("-1")).toString1() + ")"))
                    .mul(new Item("-1"));
        } else {
            return new Item("sin(" + this.toString1() + ")");
        }
    }

    public Item cos() {
        if (this.toString().equals("0")) {
            return new Item("1");
        }
        if (this.toString1().charAt(0) == '-') {
            return new Item("cos(" + this.mul(new Item("-1")).toString1() + ")");
        } else {
            return new Item("cos(" + this.toString1() + ")");
        }
    }

    public Item pow(Item otherItem) {
        Item thisItem = new Item("1");
        BigInteger i = new BigInteger("0");
        HashMap<String, BigInteger> index = new HashMap<>();
        index.put("x", new BigInteger("0"));
        for (; i.compareTo(otherItem.getExpression().get(index)) < 0;
             i = i.add(new BigInteger("1"))) {
            thisItem = thisItem.mul(this);
        }

        return thisItem;
    }

    public Item mul(Item otherItem) {
        Item thisItem = new Item("");
        for (HashMap<String, BigInteger> stringBigIntegerHashMap1 :
                otherItem.getExpression().keySet()) {
            for (HashMap<String, BigInteger> stringBigIntegerHashMap2 : this.expression.keySet()) {
                HashMap<String, BigInteger> index = new HashMap<>();
                for (String s : stringBigIntegerHashMap1.keySet()) {
                    if (stringBigIntegerHashMap2.get(s) != null) {
                        index.put(s, stringBigIntegerHashMap1.
                                get(s).add(stringBigIntegerHashMap2.get(s)));
                    } else {
                        index.put(s, stringBigIntegerHashMap1.get(s));
                    }
                }
                for (String s : stringBigIntegerHashMap2.keySet()) {
                    if (stringBigIntegerHashMap1.get(s) == null) {
                        index.put(s, stringBigIntegerHashMap2.get(s));
                    }
                }
                if (thisItem.getExpression().get(index) == null) {
                    thisItem.getExpression().put(index,
                            otherItem.getExpression().get(stringBigIntegerHashMap1).multiply(
                                    this.expression.get(stringBigIntegerHashMap2)));
                } else {
                    Item item = new Item("");
                    item.getExpression().put(index,
                            otherItem.getExpression().get(stringBigIntegerHashMap1).multiply(
                                    this.expression.get(stringBigIntegerHashMap2)));
                    thisItem = item.add(thisItem);
                }
            }
        }
        return thisItem;
    }

    public Item sub(Item otherItem) {
        Item thisItem = new Item("");
        for (HashMap<String, BigInteger> stringBigIntegerHashMap : this.expression.keySet()) {
            thisItem.getExpression().put(stringBigIntegerHashMap,
                    this.expression.get(stringBigIntegerHashMap));
        }
        for (HashMap<String, BigInteger> stringBigIntegerHashMap : otherItem
                .getExpression().keySet()) {
            if (thisItem.getExpression().get(stringBigIntegerHashMap) != null) {
                if (!this.expression.get(stringBigIntegerHashMap).subtract(otherItem.
                        getExpression().get(stringBigIntegerHashMap)).equals(new BigInteger("0"))) {
                    thisItem.getExpression().put(stringBigIntegerHashMap,
                            this.expression.get(stringBigIntegerHashMap).subtract(
                                    otherItem.getExpression().get(stringBigIntegerHashMap)));
                } else {
                    thisItem.getExpression().remove(stringBigIntegerHashMap);
                }
            } else {
                thisItem.getExpression().put(stringBigIntegerHashMap, otherItem.getExpression().get(
                        stringBigIntegerHashMap).multiply(new BigInteger("-1")));
            }
        }
        return thisItem;
    }

    public Item add(Item otherItem) {
        Item thisItem = new Item("");
        for (HashMap<String, BigInteger> stringBigIntegerHashMap : this.expression.keySet()) {
            thisItem.getExpression().put(
                    stringBigIntegerHashMap, this.expression.get(stringBigIntegerHashMap));
        }
        for (HashMap<String, BigInteger> stringBigIntegerHashMap : otherItem.
                getExpression().keySet()) {
            if (thisItem.getExpression().get(stringBigIntegerHashMap) != null) {
                if (!this.expression.get(stringBigIntegerHashMap).add(otherItem.
                        getExpression().get(stringBigIntegerHashMap)).equals(new BigInteger("0"))) {
                    thisItem.getExpression().put(stringBigIntegerHashMap,
                            this.expression.get(stringBigIntegerHashMap).add(
                                    otherItem.getExpression().get(stringBigIntegerHashMap)));
                } else {
                    thisItem.getExpression().remove(stringBigIntegerHashMap);
                }
            } else {
                thisItem.getExpression().put(stringBigIntegerHashMap,
                        otherItem.getExpression().get(stringBigIntegerHashMap));
            }
        }
        return thisItem;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        Set<HashMap<String, BigInteger>> indexSet = expression.keySet();
        ArrayList<HashMap<String, BigInteger>> sortedIndex = new ArrayList<>();
        sortedIndex.addAll(indexSet);
        sortedIndex = hashmapSort(sortedIndex);
        //  Collections.reverse(sortedIndex);
        Object del = null;
        for (Object o : sortedIndex) {
            if (!expression.get((HashMap<String, BigInteger>) o).toString().equals("0")) {
                if (expression.get((HashMap<String, BigInteger>) o).toString().charAt(0) != '-') {
                    getUp(sb, o);
                    del = o;
                    break;
                }
            }
        }
        if (del != null) {
            sortedIndex.remove(del);
        }
        for (Object o : sortedIndex) {
            if (!expression.get((HashMap<String, BigInteger>) o).toString().equals("0")) {
                if (expression.get((HashMap<String, BigInteger>) o).toString().charAt(0) != '-') {
                    sb.append("+");
                }
                getUp(sb, o);
            }
        }
        if (sb.toString().length() == 0) {
            return "0";
        } else {
            return sb.toString();
        }
    }

    private ArrayList<HashMap<String, BigInteger>> hashmapSort(
            ArrayList<HashMap<String, BigInteger>> sortedIndex) {
        Collections.sort(sortedIndex, new Comparator<Object>() {
            @Override
            public int compare(Object o1, Object o2) {
                ArrayList<String> sortedListSet1 = new ArrayList<>();
                Set<String> set1 = ((HashMap<String, BigInteger>) o1).keySet();
                TreeSet<String> sortedSet1 = new TreeSet<>();
                sortedSet1.addAll(set1);
                sortedListSet1.addAll(sortedSet1);
                ArrayList<String> sortedListSet2 = new ArrayList<>();
                Set<String> set2 = ((HashMap<String, BigInteger>) o2).keySet();
                TreeSet<String> sortedSet2 = new TreeSet<>();
                sortedSet2.addAll(set2);
                sortedListSet2.addAll(sortedSet2);
                if (sortedListSet1.size() == 0) {
                    return -1;
                }
                if (sortedListSet2.size() == 0) {
                    return 1;
                }
                int flag = 0;
                while (flag < sortedListSet1.size() && flag < sortedListSet2.size()) {
                    if (sortedListSet1.get(flag).compareTo(sortedListSet2.get(flag)) < 0) {
                        return -1;
                    } else if (sortedListSet1.get(flag).compareTo(sortedListSet2.get(flag)) > 0) {
                        return 1;
                    } else {
                        if (((HashMap<String, BigInteger>) o1).get(sortedListSet1.get(flag)).
                                compareTo(((HashMap<String, BigInteger>) o2).
                                        get(sortedListSet2.get(flag))) < 0) {
                            return 1;
                        } else if (((HashMap<String, BigInteger>) o1).get(sortedListSet1.get(flag)).
                                compareTo(((HashMap<String, BigInteger>) o2).
                                        get(sortedListSet2.get(flag))) > 0) {
                            return -1;
                        } else {
                            flag++;
                        }
                    }
                }
                if (flag >= sortedListSet2.size()) {
                    return 1;
                } else {
                    return -1;
                }
            }
        });
        return sortedIndex;
    }

    private void getUp(StringBuilder sb, Object o) {
        StringBuilder sb1 = new StringBuilder();
        if (expression.get((HashMap<String, BigInteger>) o).toString().equals("-1")) {
            sb1.append("-");
        } else if (!expression.get((HashMap<String, BigInteger>) o).toString().equals("1")) {
            sb1.append(expression.get((HashMap<String, BigInteger>) o).toString() + "*");
        }
        Set<String> set = ((HashMap<String, BigInteger>) o).keySet();
        TreeSet<String> sortedSet = new TreeSet<>();
        sortedSet.addAll(set);
        for (Object j : sortedSet) {
            if (!(((HashMap<String, BigInteger>) o).get(j)).equals(new BigInteger("0"))) {
                if ((((HashMap<String, BigInteger>) o).get(j)).equals(new BigInteger("1"))) {
                    sb1.append(j + "*");
                } else if ((((HashMap<String, BigInteger>) o).get(j)).equals(new BigInteger("2"))) {
                    if (j.toString().length() == 1) {
                        sb1.append(j + "*" + j + "*");
                    } else {
                        sb1.append(j + "**" + ((HashMap<String, BigInteger>) o).get(j) + "*");
                    }
                } else {
                    sb1.append(j + "**" + ((HashMap<String, BigInteger>) o).get(j) + "*");
                }
            }
        }
        if (sb1.toString().length() <= 1) {
            sb.append(sb1.toString() + "1");
        } else {
            sb.append(sb1.toString(), 0, sb1.toString().length() - 1);
        }
    }

    public HashMap<HashMap<String, BigInteger>, BigInteger> getExpression() {
        return expression;
    }

    public void setExpression(HashMap<HashMap<String, BigInteger>, BigInteger> expression) {
        this.expression = expression;
    }

    public String toString1() {
        StringBuilder sb = new StringBuilder();
        Set<HashMap<String, BigInteger>> indexSet = expression.keySet();
        ArrayList<HashMap<String, BigInteger>> sortedIndex = new ArrayList<>();
        sortedIndex.addAll(indexSet);
        sortedIndex = hashmapSort(sortedIndex);
        //  Collections.reverse(sortedIndex);
        Object del = null;
        for (Object o : sortedIndex) {
            if (!expression.get((HashMap<String, BigInteger>) o).toString().equals("0")) {
                if (expression.get((HashMap<String, BigInteger>) o).toString().charAt(0) != '-') {
                    getUp1(sb, o);
                    del = o;
                    break;
                }
            }
        }
        if (del != null) {
            sortedIndex.remove(del);
        }
        for (Object o : sortedIndex) {
            if (!expression.get((HashMap<String, BigInteger>) o).toString().equals("0")) {
                if (expression.get((HashMap<String, BigInteger>) o).toString().charAt(0) != '-') {
                    sb.append("+");
                }
                getUp1(sb, o);
            }
        }
        if (sb.toString().length() == 0) {
            return "0";
        } else {
            return sb.toString();
        }
    }

    private void getUp1(StringBuilder sb, Object o) {
        StringBuilder sb1 = new StringBuilder();
        if (expression.get((HashMap<String, BigInteger>) o).toString().equals("-1")) {
            sb1.append("-");
        } else if (!expression.get((HashMap<String, BigInteger>) o).toString().equals("1")) {
            sb1.append(expression.get((HashMap<String, BigInteger>) o).toString() + "*");
        }
        Set<String> set = ((HashMap<String, BigInteger>) o).keySet();
        TreeSet<String> sortedSet = new TreeSet<>();
        sortedSet.addAll(set);
        for (Object j : sortedSet) {
            if (!(((HashMap<String, BigInteger>) o).get(j)).equals(new BigInteger("0"))) {
                if ((((HashMap<String, BigInteger>) o).get(j)).equals(new BigInteger("1"))) {
                    sb1.append(j + "*");
                } else {
                    sb1.append(j + "**" + ((HashMap<String, BigInteger>) o).get(j) + "*");
                }
            }
        }
        if (sb1.toString().length() <= 1) {
            sb.append(sb1.toString() + "1");
        } else {
            sb.append(sb1.toString(), 0, sb1.toString().length() - 1);
        }
    }
}
