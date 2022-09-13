package com.oocourse.uml2.utils.string;

import java.util.Collections;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * 字符串构建工具类
 */
abstract class StringProcessUtils {
    /**
     * 添加重复词
     *
     * @param builder 字符串构建对象
     * @param word    单词
     * @param times   重复次数
     */
    static void appendRepeatedWords(StringBuilder builder, String word, int times) {
        appendJoinedWords(builder, Collections.nCopies(times, word));
    }

    /**
     * 添加连接单词串
     *
     * @param builder 字符串构建对象
     * @param objects 对象迭代器
     * @param <T>     对象类型
     */
    static <T> void appendJoinedWords(StringBuilder builder, Iterable<T> objects) {
        appendJoinedWords(builder, objects, Collectors.joining());
    }

    /**
     * 添加连接单词串
     *
     * @param builder   字符串构建对象
     * @param objects   对象迭代器
     * @param delimiter 分隔符
     * @param <T>       对象类型
     */
    static <T> void appendJoinedWords(StringBuilder builder, Iterable<T> objects, String delimiter) {
        appendJoinedWords(builder, objects, Collectors.joining(delimiter));
    }

    /**
     * 添加连接单词串
     *
     * @param builder   字符串构建对象
     * @param objects   对象迭代器
     * @param delimiter 分隔符
     * @param prefix    前缀符号
     * @param suffix    后缀读好
     * @param <T>       对象类型
     */
    static <T> void appendJoinedWords(StringBuilder builder, Iterable<T> objects, String delimiter, String prefix, String suffix) {
        appendJoinedWords(builder, objects, Collectors.joining(delimiter, prefix, suffix));
    }

    /**
     * 添加连接单词串
     *
     * @param builder   字符串构建对象
     * @param objects   对象迭代器
     * @param collector 收集器
     * @param <T>       对象类型
     */
    private static <T> void appendJoinedWords(StringBuilder builder, Iterable<T> objects, Collector<CharSequence, ?, String> collector) {
        builder.append(
                StreamSupport.stream(objects.spliterator(), false)
                        .map(Object::toString).collect(collector)
        );
    }

}
