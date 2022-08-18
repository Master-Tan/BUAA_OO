package com.oocourse.uml2.utils.string.table;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * 表行对象
 *
 * @param <T> 对象类型
 */
@SuppressWarnings("WeakerAccess")
public abstract class TableAbstractRow<T> implements Iterable<T> {
    private final List<T> itemList;

    /**
     * 构造函数
     *
     * @param itemList  对象列表
     * @param transform 对象转换方法
     */
    protected TableAbstractRow(List<Object> itemList, Function<Object, T> transform) {
        this.itemList = Collections.unmodifiableList(
                itemList.stream().map(transform).collect(Collectors.toList())
        );
    }

    /**
     * 对象数量
     *
     * @return 数量
     */
    public int size() {
        return this.itemList.size();
    }

    /**
     * 获取指定位置的对象
     *
     * @param index 位置编号
     * @return 对象
     */
    public T getItem(int index) {
        return this.itemList.get(index);
    }

    /**
     * 获取迭代器
     *
     * @return 迭代器
     */
    @Override
    public Iterator<T> iterator() {
        return this.itemList.iterator();
    }

    /**
     * 获取函数式流
     *
     * @return 函数式流
     */
    Stream<T> stream() {
        return this.itemList.stream();
    }

    /**
     * 转为字符串形式
     *
     * @return 字符串形式
     */
    @Override
    public String toString() {
        return this.itemList.stream().map(T::toString)
                .collect(Collectors.joining(Table.ROW_DELIMITER, Table.ROW_PREFIX, Table.ROW_SUFFIX));
    }

    /**
     * 相等性判断
     *
     * @param o 对象
     * @return 是否相等
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        TableAbstractRow<?> that = (TableAbstractRow<?>) o;
        return Objects.equals(itemList, that.itemList);
    }

    /**
     * 获取哈希值
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Objects.hash(itemList);
    }
}
