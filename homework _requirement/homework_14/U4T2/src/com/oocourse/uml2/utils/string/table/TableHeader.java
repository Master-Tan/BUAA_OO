package com.oocourse.uml2.utils.string.table;

import com.oocourse.uml2.utils.common.GenericContainer;

import java.util.Arrays;
import java.util.List;

/**
 * 表头对象
 */
public class TableHeader extends TableAbstractRow<TableHeader.TableHeaderItem> {
    /**
     * 构造函数
     *
     * @param itemList 表头信息
     */
    public TableHeader(List<Object> itemList) {
        super(itemList, TableHeaderItem::new);
    }

    /**
     * 构造函数
     *
     * @param items 表头信息
     */
    public TableHeader(Object... items) {
        this(Arrays.asList(items));
    }

    /**
     * 表头项
     *
     * @param <T> 类型
     */
    public static class TableHeaderItem<T> extends GenericContainer<T> {
        /**
         * 构造函数
         *
         * @param item 对象
         */
        TableHeaderItem(T item) {
            super(item);
        }

        /**
         * 获取对象
         *
         * @return 对象
         */
        public T getItem() {
            return super.getContent();
        }

        /**
         * 转为字符串形式
         *
         * @return 字符串形式
         */
        @Override
        public String toString() {
            return (super.getContent() == null || super.getContent().toString() == null) ? ""
                    : super.getContent().toString();
        }
    }
}
