import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class TriSimplify {

    private Item expression;

    public TriSimplify(Item expression) {
        this.expression = expression;
    }

    public Item simplify() {

        Item calculatedExpression = this.expression;
        Item simplifyExpression = new Item("");
        simplifyExpression.setExpression(calculatedExpression.getExpression());

        simplifyExpression = clean(simplifyExpression);
        // 数据清除
        //  System.out.println(simplifyExpression);

        while (true) {

            Item newPassExpression;
            newPassExpression = getNew(simplifyExpression);

            simplifyExpression = simplify1(simplifyExpression);
            if (newPassExpression.toString().length() < simplifyExpression.toString().length()) {
                simplifyExpression = newPassExpression;
            }
            //  化简sin(x)**2+cos(x)**2

            //  System.out.println(simplifyExpression);
            //  化简1-cos(x)**2=sin(x)**2
            while (true) {
                Item passExpression = getNew(simplifyExpression);
                simplifyExpression = simplify2(simplifyExpression);
                if (passExpression.toString().length() == simplifyExpression.toString().length()) {
                    break;
                } else if (passExpression.toString().length() <
                        simplifyExpression.toString().length()) {
                    simplifyExpression = passExpression;
                    break;
                }
            }
            //  System.out.println(simplifyExpression);
            //  化简2*sin(1)*cos(1)=cos(2)
            while (true) {
                Item passExpression = getNew(simplifyExpression);
                simplifyExpression = simplify3(simplifyExpression);
                if (passExpression.toString().length() == simplifyExpression.toString().length()) {
                    break;
                } else if (passExpression.toString().length() <
                        simplifyExpression.toString().length()) {
                    simplifyExpression = passExpression;
                    break;
                }
            }
            //  System.out.println(simplifyExpression);

            if (newPassExpression.toString().length() == simplifyExpression.toString().length()) {
                break;
            } else if (newPassExpression.toString().length() <
                    simplifyExpression.toString().length()) {
                simplifyExpression = newPassExpression;
                break;
            }
        }

        return simplifyExpression;
    }

    private Item getNew(Item simplifyExpression) {
        Item passExpression = new Item("");
        for (HashMap<String, BigInteger> hashMap : simplifyExpression.
                getExpression().keySet()) {
            HashMap<String, BigInteger> newHashMap = new HashMap<>();
            for (String s : hashMap.keySet()) {
                newHashMap.put(s, hashMap.get(s));
            }
            passExpression.getExpression().put(
                    newHashMap, simplifyExpression.getExpression().get(hashMap));
        }
        return passExpression;
    }

    private Item clean(Item expression) {
        Item simplifyExpression = expression;
        ArrayList<HashMap<String, BigInteger>> del = new ArrayList<>();
        for (HashMap<String, BigInteger> stringBigIntegerHashMap :
                simplifyExpression.getExpression().keySet()) {
            if (stringBigIntegerHashMap.size() > 1) {
                if (stringBigIntegerHashMap.get("x") != null) {
                    if (stringBigIntegerHashMap.get("x").equals(new BigInteger("0"))) {
                        del.add(stringBigIntegerHashMap);
                    }
                }
            }
        }
        for (HashMap<String, BigInteger> stringBigIntegerHashMap : del) {
            HashMap<String, BigInteger> newItem = new HashMap<>();
            for (String s : stringBigIntegerHashMap.keySet()) {
                newItem.put(s, stringBigIntegerHashMap.get(s));
            }
            newItem.remove("x");
            BigInteger bigInteger = simplifyExpression.
                    getExpression().get(stringBigIntegerHashMap);
            Item item = new Item("");
            item.getExpression().put(newItem, bigInteger);
            simplifyExpression.getExpression().remove(stringBigIntegerHashMap);
            simplifyExpression = simplifyExpression.add(item);
        }
        return simplifyExpression;
    }

    private Item simplify3(Item expression) {
        Item simplifyExpression = new Item("");
        simplifyExpression.setExpression(expression.getExpression());
        Pattern sinPattern = Pattern.compile("^sin\\(");
        Pattern cosPattern = Pattern.compile("^cos\\(");

        ArrayList<HashMap<String, BigInteger>> del = new ArrayList<>();
        ArrayList<HashMap<String, BigInteger>> hashMapList = new ArrayList<>();
        ArrayList<String> stringList = new ArrayList<>();
        ArrayList<Integer> cntList = new ArrayList<>();

        for (HashMap<String, BigInteger> stringBigIntegerHashMap :
                simplifyExpression.getExpression().keySet()) {
            if (simplifyExpression.getExpression().get(stringBigIntegerHashMap)
                    .mod(new BigInteger("2")).equals(new BigInteger("0"))) {
                for (String s1 : stringBigIntegerHashMap.keySet()) {
                    for (String s2 : stringBigIntegerHashMap.keySet()) {
                        Matcher sinMatcher = sinPattern.matcher(s1);
                        Matcher cosMatcher = cosPattern.matcher(s2);
                        if (sinMatcher.find() && cosMatcher.find() &&
                                s1.substring(4).equals(s2.substring(4))) {
                            if (stringBigIntegerHashMap.get(s1).equals(
                                    stringBigIntegerHashMap.get(s2))) {
                                BigInteger bigint = simplifyExpression.getExpression().get(
                                        stringBigIntegerHashMap).abs();
                                int flag1 = 1;
                                BigInteger cnt1 = new BigInteger("0");
                                while (cnt1.compareTo(stringBigIntegerHashMap.get(s1)) < 0) {
                                    if (bigint.mod(new BigInteger("2")).
                                            equals(new BigInteger("0"))) {
                                        cnt1 = cnt1.add(new BigInteger("1"));
                                        bigint = bigint.divide(new BigInteger("2"));
                                    } else {
                                        flag1 = 0;
                                        break;
                                    }
                                }
                                if (flag1 == 1) {
                                    HashMap<String, BigInteger> hashMap = new HashMap<>();
                                    for (String s : stringBigIntegerHashMap.keySet()) {
                                        hashMap.put(s, stringBigIntegerHashMap.get(s));
                                    }
                                    int cnt = 0;
                                    cnt = calcuate(hashMap, s1, s2);
                                    del.add(stringBigIntegerHashMap);
                                    hashMapList.add(hashMap);
                                    stringList.add(s1.substring(4, s1.length() - 1));
                                    cntList.add(cnt);
                                }
                            }
                        }
                    }
                }
            }
        }
        simplifyExpression = delete3(simplifyExpression, del, hashMapList, stringList, cntList);
        return simplifyExpression;
    }

    private int calcuate(HashMap<String, BigInteger> hashMap, String s1, String s2) {

        int cnt = 0;
        while (hashMap.get(s1) != null) {
            if (hashMap.get(s1).compareTo(new BigInteger("0")) > 0) {
                rm3(hashMap, s1);
                rm3(hashMap, s2);
                cnt++;
            } else {
                break;
            }
        }

        return cnt;
    }

    private Item delete3(Item expression,
                         ArrayList<HashMap<String, BigInteger>> del,
                         ArrayList<HashMap<String, BigInteger>> hashMapList,
                         ArrayList<String> stringList, ArrayList<Integer> num) {
        Item simplifyExpression = new Item("");
        simplifyExpression.setExpression(expression.getExpression());
        if (del.size() > 0) {
            int i = 0;
            int cnt = num.get(i);
            BigInteger bigInteger = new BigInteger(simplifyExpression.
                    getExpression().get(del.get(i)).toString());
            BigInteger bigInteger1 = new BigInteger(bigInteger.toString());
            for (int j = 0; j < cnt; j++) {
                bigInteger1 = new BigInteger(
                        bigInteger1.divide(new BigInteger("2")).toString());
            }
            simplifyExpression.getExpression().remove(del.get(i));
            Item item = new Item("");
            item.getExpression().put(hashMapList.get(i), bigInteger1);
            Item item1 = new Item(stringList.get(i)).mul(new Item("2")).sin();
            for (int j = 0; j < cnt; j++) {
                item = item.mul(item1);
            }
            simplifyExpression = simplifyExpression.add(item);
        }
        return simplifyExpression;
    }

    private void rm3(HashMap<String, BigInteger> hashMap, String s) {
        if (hashMap.get(s).equals(new BigInteger("1"))) {
            hashMap.remove(s);
            if (hashMap.size() == 0) {
                hashMap.put("x", new BigInteger("0"));
            }
        } else {
            hashMap.put(s, hashMap.get(s).subtract(
                    new BigInteger("1")));
        }
    }

    private Item simplify2(Item expression) {
        Item simplifyExpression = new Item("");
        simplifyExpression.setExpression(expression.getExpression());

        Pattern sinPattern = Pattern.compile("^sin\\(");
        Pattern cosPattern = Pattern.compile("^cos\\(");

        ArrayList<HashMap<String, BigInteger>> del1 = new ArrayList<>();
        ArrayList<HashMap<String, BigInteger>> del2 = new ArrayList<>();
        ArrayList<HashMap<String, BigInteger>> hashMapList = new ArrayList<>();
        ArrayList<String> stringList = new ArrayList<>();
        for (HashMap<String, BigInteger> stringBigIntegerHashMap1 :
                simplifyExpression.getExpression().keySet()) {
            for (HashMap<String, BigInteger> stringBigIntegerHashMap2 :
                    simplifyExpression.getExpression().keySet()) {
                for (String s1 : stringBigIntegerHashMap1.keySet()) {
                    Matcher sinMatcher = sinPattern.matcher(s1);
                    Matcher cosMatcher = cosPattern.matcher(s1);
                    if (sinMatcher.find() | cosMatcher.find()) {
                        HashMap<String, BigInteger> hashMap1 = new HashMap<>();
                        HashMap<String, BigInteger> hashMap2 = new HashMap<>();
                        for (String s : stringBigIntegerHashMap1.keySet()) {
                            hashMap1.put(s, stringBigIntegerHashMap1.get(s));
                        }
                        for (String s : stringBigIntegerHashMap2.keySet()) {
                            hashMap2.put(s, stringBigIntegerHashMap2.get(s));
                        }
                        if (hashMap1.get(s1).equals(new BigInteger("2"))) {
                            hashMap1.remove(s1);
                            if (hashMap1.size() == 0) {
                                hashMap1.put("x", new BigInteger("0"));
                            }
                            if (hashMap1.equals(hashMap2)) {
                                del1.add(stringBigIntegerHashMap1);
                                del2.add(stringBigIntegerHashMap2);
                                hashMapList.add((hashMap1));
                                stringList.add(s1);
                            }
                        }
                    }
                }
            }
        }
        simplifyExpression = delete2(simplifyExpression, del1, del2, hashMapList, stringList);
        return simplifyExpression;
    }

    private static Item delete2(Item expression,
                                ArrayList<HashMap<String, BigInteger>> del1,
                                ArrayList<HashMap<String, BigInteger>> del2,
                                ArrayList<HashMap<String, BigInteger>> hashMapList,
                                ArrayList<String> stringList) {
        Item simplifyExpression = new Item("");
        simplifyExpression.setExpression(expression.getExpression());
        if (del1.size() > 0) {
            int i = 0;
            BigInteger bigInteger1 = new BigInteger(simplifyExpression.
                    getExpression().get(del1.get(i)).toString());
            BigInteger bigInteger2 = new BigInteger(simplifyExpression.
                    getExpression().get(del2.get(i)).toString());
            Pattern sinPattern = Pattern.compile("^sin\\(");
            Pattern cosPattern = Pattern.compile("^cos\\(");
            Matcher sinMatcher = sinPattern.matcher(stringList.get(i));
            Matcher cosMatcher = cosPattern.matcher(stringList.get(i));
            String s = "";
            if (sinMatcher.find()) {
                s = stringList.get(i).replaceAll("^sin", "cos");
            } else if (cosMatcher.find()) {
                s = stringList.get(i).replaceAll("^cos", "sin");
            }
            int flag = 0;
            if (bigInteger2.add(bigInteger1).toString().length() <
                    bigInteger2.toString().length()) {
                flag = 1;
            } else if (bigInteger2.add(bigInteger1).toString().length() ==
                    bigInteger2.toString().length()) {
                if (bigInteger1.compareTo(new BigInteger("0")) < 0) {
                    flag = 1;
                }
            }
            if (flag == 1) {
                simplifyExpression.getExpression().remove(del1.get(i));
                simplifyExpression.getExpression().remove(del2.get(i));
                Item item1 = new Item("");
                item1.getExpression().put(hashMapList.get(i), bigInteger2.add(bigInteger1));
                Item item2 = new Item("");
                item2.getExpression().put(hashMapList.get(i),
                        bigInteger1.multiply(new BigInteger("-1")));
                item2 = item2.mul(new Item(s).pow(new Item("2")));
                simplifyExpression = simplifyExpression.add(item1).add(item2);
            }
        }
        return simplifyExpression;
    }

    private Item simplify1(Item expression) {
        Item simplifyExpression = new Item("");
        simplifyExpression.setExpression(expression.getExpression());

        int flag = 1;
        while (flag == 1) {
            flag = 0;
            Set<HashMap<String, BigInteger>> indexSet = simplifyExpression.getExpression().keySet();
            ArrayList<HashMap<String, BigInteger>> sortedIndex = new ArrayList<>();
            sortedIndex.addAll(indexSet);
            sortedIndex = hashmapSort(sortedIndex);


            Pattern sinPattern = Pattern.compile("^sin\\(");
            Pattern cosPattern = Pattern.compile("^cos\\(");

            ArrayList<HashMap<String, BigInteger>> del1 = new ArrayList<>();
            ArrayList<HashMap<String, BigInteger>> del2 = new ArrayList<>();
            ArrayList<HashMap<String, BigInteger>> hashMapList = new ArrayList<>();
            for (HashMap<String, BigInteger> stringBigIntegerHashMap1 : sortedIndex) {
                for (HashMap<String, BigInteger> stringBigIntegerHashMap2 : sortedIndex) {
                    for (String s1 : stringBigIntegerHashMap1.keySet()) {
                        for (String s2 : stringBigIntegerHashMap2.keySet()) {
                            Matcher sinMatcher = sinPattern.matcher(s1);
                            Matcher cosMatcher = cosPattern.matcher(s2);
                            if (sinMatcher.find() && cosMatcher.find()) {
                                HashMap<String, BigInteger> hashMap1 = new HashMap<>();
                                HashMap<String, BigInteger> hashMap2 = new HashMap<>();
                                for (String s : stringBigIntegerHashMap1.keySet()) {
                                    hashMap1.put(s, stringBigIntegerHashMap1.get(s));
                                }
                                for (String s : stringBigIntegerHashMap2.keySet()) {
                                    hashMap2.put(s, stringBigIntegerHashMap2.get(s));
                                }
                                rm(hashMap1, s1);
                                rm(hashMap2, s2);
                                if (hashMap1.equals(hashMap2)) {
                                    if (s1.substring(4).equals(s2.substring(4))) {
                                        del1.add(stringBigIntegerHashMap1);
                                        del2.add(stringBigIntegerHashMap2);
                                        hashMapList.add((hashMap1));
                                        flag = 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            simplifyExpression = delete1(simplifyExpression, del1, del2, hashMapList);
        }


        return simplifyExpression;
    }

    private void rm(HashMap<String, BigInteger> hashMap, String s) {
        if (hashMap.get(s).equals(new BigInteger("2"))) {
            hashMap.remove(s);
            if (hashMap.size() == 0) {
                hashMap.put("x", new BigInteger("0"));
            }
        } else {
            hashMap.put(s, hashMap.get(s).subtract(
                    new BigInteger("2")));
        }
    }

    private static Item delete1(Item expression,
                                ArrayList<HashMap<String, BigInteger>> del1,
                                ArrayList<HashMap<String, BigInteger>> del2,
                                ArrayList<HashMap<String, BigInteger>> hashMapList) {
        Item simplifyExpression = new Item("");
        simplifyExpression.setExpression(expression.getExpression());
        if (del1.size() > 0) {
            int i = 0;
            BigInteger bigInteger1 = new BigInteger(simplifyExpression.
                    getExpression().get(del1.get(i)).toString());
            BigInteger bigInteger2 = new BigInteger(simplifyExpression.
                    getExpression().get(del2.get(i)).toString());
            if (bigInteger1.compareTo(bigInteger2) < 0) {
                BigInteger bigInteger = new BigInteger(bigInteger1.toString());
                simplifyExpression.getExpression().remove(del1.get(i));
                simplifyExpression.getExpression().remove(del2.get(i));
                Item item = new Item("");
                item.getExpression().put(hashMapList.get(i), bigInteger);
                simplifyExpression = simplifyExpression.add(item);
                simplifyExpression.getExpression().put(
                        del2.get(i), bigInteger2.subtract(bigInteger1));
            } else if (bigInteger1.compareTo(bigInteger2) == 0) {
                BigInteger bigInteger = new BigInteger(bigInteger1.toString());
                simplifyExpression.getExpression().remove(del1.get(i));
                simplifyExpression.getExpression().remove(del2.get(i));
                Item item = new Item("");
                item.getExpression().put(hashMapList.get(i), bigInteger);
                simplifyExpression = simplifyExpression.add(item);
            } else {
                BigInteger bigInteger = new BigInteger(bigInteger2.toString());
                simplifyExpression.getExpression().remove(del1.get(i));
                simplifyExpression.getExpression().remove(del2.get(i));
                Item item = new Item("");
                item.getExpression().put(hashMapList.get(i), bigInteger);
                simplifyExpression = simplifyExpression.add(item);
                simplifyExpression.getExpression().put(
                        del1.get(i), bigInteger1.subtract(bigInteger2));
            }
        }
        return simplifyExpression;
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

}
