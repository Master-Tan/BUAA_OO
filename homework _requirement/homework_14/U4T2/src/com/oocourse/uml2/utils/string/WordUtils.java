package com.oocourse.uml2.utils.string;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * 单词变换类
 */
public abstract class WordUtils {
    private static final Pattern CAMEL_PATTERN = Pattern.compile("[A-Za-z][a-z0-9]*");
    private static final String UNDERLINE = "_";

    /**
     * 单个词首字母大写
     *
     * @param originalWord 原词
     * @return 首字母大写单词
     */
    private static String capitalizeSingleWord(String originalWord) {
        if (originalWord == null || originalWord.length() == 0) {
            return originalWord;
        } else {
            return originalWord.substring(0, 1).toUpperCase()
                    + originalWord.substring(1).toLowerCase();
        }
    }

    /**
     * 从下划线命名法中获取单词
     *
     * @param original 原命名
     * @return 单词列表
     */
    public static List<String> getWordsFromUnderline(String original) {
        return Stream.of(original.split(UNDERLINE))
                .map(String::toLowerCase)
                .collect(Collectors.toList());
    }

    /**
     * 从驼峰命名法中获取词汇
     *
     * @param original 原命名
     * @return 单词列表
     */
    public static List<String> getWordsFromCamel(String original) {
        Matcher matcher = CAMEL_PATTERN.matcher(original);
        List<String> words = new ArrayList<>();
        while (matcher.find()) {
            String word = matcher.group();
            words.add(word.toLowerCase());
        }
        return words;
    }

    /**
     * 单词列表转大驼峰
     *
     * @param wordList 单词列表
     * @return 大驼峰
     */
    public static String getLargeCamelFromList(List<String> wordList) {
        return wordList.stream().map(WordUtils::capitalizeSingleWord)
                .collect(Collectors.joining());
    }

    /**
     * 单词列表转小驼峰
     *
     * @param wordList 单词列表
     * @return 小驼峰
     */
    public static String getSmallCamelFromList(List<String> wordList) {
        return IntStream.range(0, wordList.size()).boxed()
                .map(index -> (index == 0) ? wordList.get(index).toLowerCase()
                        : capitalizeSingleWord(wordList.get(index)))
                .collect(Collectors.joining());
    }

    /**
     * 单词列表转大写下划线
     *
     * @param wordList 单词列表
     * @return 大写下划线
     */
    public static String getLargeUnderlineFromList(List<String> wordList) {
        return wordList.stream().map(String::toUpperCase)
                .collect(Collectors.joining(UNDERLINE));
    }

    /**
     * 单词列表转小写下划线
     *
     * @param wordList 单词列表
     * @return 小写下划线
     */
    public static String getSmallUnderlineFromList(List<String> wordList) {
        return wordList.stream().map(String::toLowerCase)
                .collect(Collectors.joining(UNDERLINE));
    }
}
