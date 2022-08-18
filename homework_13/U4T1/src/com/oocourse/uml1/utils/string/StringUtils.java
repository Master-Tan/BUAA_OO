package com.oocourse.uml1.utils.string;

import java.util.ArrayList;
import java.util.Collections;
import java.util.function.Function;

public abstract class StringUtils {
    public static <T> String joinWithTransform(T[] elements, Function<T, String> transformer, String splitter) {
        ArrayList<T> list = new ArrayList<>();
        Collections.addAll(list, elements);
        return joinWithTransform(list, transformer, splitter);
    }

    public static <T> String joinWithTransform(Iterable<T> iterable, Function<T, String> transformer, String splitter) {
        boolean first = true;
        StringBuilder builder = new StringBuilder();
        for (T item : iterable) {
            if (first) {
                first = false;
            } else {
                builder.append(splitter);
            }
            builder.append(transformer.apply(item));
        }
        return builder.toString();
    }

    public static String repeatString(String word, int times) {
        StringBuilder builder = new StringBuilder();
        for (int i = 0; i < times; i++) {
            builder.append(word);
        }
        return builder.toString();
    }

    public static String fillWhiteSpaceAlignLeft(String word, int length) {
        StringBuilder builder = new StringBuilder();
        builder.append(word);
        for (int i = word.length(); i < length; i++) {
            builder.append(" ");
        }
        return builder.toString();
    }

    public static String fillWhiteSpaceAlignRight(String word, int length) {
        StringBuilder builder = new StringBuilder();
        for (int i = word.length(); i < length; i++) {
            builder.append(" ");
        }
        builder.append(word);
        return builder.toString();
    }

    public static String fillWhiteSpaceAlignMiddle(String word, int length) {
        StringBuilder builder = new StringBuilder();
        int totalSpaceLength = length - word.length();
        int leftLength = totalSpaceLength / 2;
        int rightLength = totalSpaceLength - leftLength;
        for (int i = 0; i < leftLength; i++) {
            builder.append(" ");
        }
        builder.append(word);
        for (int i = 0; i < rightLength; i++) {
            builder.append(" ");
        }
        return builder.toString();
    }
}
