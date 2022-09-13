import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
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

        // 数据清除
        ArrayList<HashMap<String, BigInteger>> del = new ArrayList<>();
        for (HashMap<String, BigInteger> stringBigIntegerHashMap :
                calculatedExpression.getExpression().keySet()) {
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


        while (true) {
            int num = 0;
            num = simplifyExpression.toString().length();

            //  化简sin(x)**2+cos(x)**2
            simplifyExpression = simplify1(simplifyExpression);
            //  化简1-cos(x)**2=sin(x)**2
            simplifyExpression = simplify2(simplifyExpression);
            //  化简2*sin(1)*cos(1)=cos(2)
            simplifyExpression = simplify3(simplifyExpression);

            if (num <= simplifyExpression.toString().length()) {
                break;
            }
        }

        return simplifyExpression;
    }

    private Item simplify3(Item expression) {
        Item simplifyExpression = new Item("");
        simplifyExpression.setExpression(expression.getExpression());
        Pattern sinPattern = Pattern.compile("^sin\\(");
        Pattern cosPattern = Pattern.compile("^cos\\(");

        Pattern numPattern = Pattern.compile("^([+]|[-])?\\d+\\)$");

        int flag = 1;
        while (flag == 1) {

            flag = 0;

            ArrayList<HashMap<String, BigInteger>> del = new ArrayList<>();
            ArrayList<HashMap<String, BigInteger>> hashMapList = new ArrayList<>();
            ArrayList<String> stringList = new ArrayList<>();
            for (HashMap<String, BigInteger> stringBigIntegerHashMap :
                    simplifyExpression.getExpression().keySet()) {
                if (simplifyExpression.getExpression().get(stringBigIntegerHashMap)
                        .mod(new BigInteger("2")).equals(new BigInteger("0"))) {
                    for (String s1 : stringBigIntegerHashMap.keySet()) {
                        for (String s2 : stringBigIntegerHashMap.keySet()) {
                            Matcher sinMatcher = sinPattern.matcher(s1);
                            Matcher cosMatcher = cosPattern.matcher(s2);
                            if (sinMatcher.find() && cosMatcher.find()) {
                                HashMap<String, BigInteger> hashMap = new HashMap<>();
                                for (String s : stringBigIntegerHashMap.keySet()) {
                                    hashMap.put(s, stringBigIntegerHashMap.get(s));
                                }
                                rm3(hashMap, s1);
                                rm3(hashMap, s2);
                                if (s1.substring(4).equals(s2.substring(4))) {
                                    Matcher numMatcher = numPattern.matcher(s1.substring(4));
                                    if (numMatcher.find()) {
                                        del.add(stringBigIntegerHashMap);
                                        hashMapList.add(hashMap);
                                        stringList.add(s1.substring(4, s1.length() - 1));
                                        flag = 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            simplifyExpression = delete3(simplifyExpression, del, hashMapList, stringList);
        }

        return simplifyExpression;
    }

    private Item delete3(Item expression,
                         ArrayList<HashMap<String, BigInteger>> del,
                         ArrayList<HashMap<String, BigInteger>> hashMapList,
                         ArrayList<String> stringList) {
        Item simplifyExpression = new Item("");
        simplifyExpression.setExpression(expression.getExpression());
        if (del.size() > 0) {
            int i = 0;
            BigInteger bigInteger = new BigInteger(simplifyExpression.
                    getExpression().get(del.get(i)).toString());
            BigInteger bigInteger1 = new BigInteger(
                    bigInteger.divide(new BigInteger("2")).toString());
            simplifyExpression.getExpression().remove(del.get(i));
            Item item = new Item("");
            item.getExpression().put(hashMapList.get(i), bigInteger1);
            item = item.mul(new Item(stringList.get(i)).mul(new Item("2")).sin());
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
        Pattern sinPattern = Pattern.compile("^sin\\(");
        Pattern cosPattern = Pattern.compile("^cos\\(");

        int flag = 1;
        while (flag == 1) {

            flag = 0;

            ArrayList<HashMap<String, BigInteger>> del1 = new ArrayList<>();
            ArrayList<HashMap<String, BigInteger>> del2 = new ArrayList<>();
            ArrayList<HashMap<String, BigInteger>> hashMapList = new ArrayList<>();
            for (HashMap<String, BigInteger> stringBigIntegerHashMap1 :
                    simplifyExpression.getExpression().keySet()) {
                for (HashMap<String, BigInteger> stringBigIntegerHashMap2 :
                        simplifyExpression.getExpression().keySet()) {
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

}
