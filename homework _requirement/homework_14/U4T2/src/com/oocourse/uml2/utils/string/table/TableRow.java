package com.oocourse.uml2.utils.string.table;

import com.oocourse.uml2.utils.common.GenericContainer;

import java.util.Arrays;
import java.util.List;

/**
 * 表行
 */
public class TableRow extends TableAbstractRow<TableRow.TableRowItem> {
    /**
     * 构造函数
     *
     * @param itemList 表行信息
     */
    public TableRow(List<Object> itemList) {
        super(itemList, TableRowItem::new);
    }

    /**
     * 构造函数
     *
     * @param itemList 表行信息
     */
    public TableRow(Object... itemList) {
        this(Arrays.asList(itemList));
    }

    /**
     * 表行项
     *
     * @param <T> 类型
     */
    public static class TableRowItem<T> extends GenericContainer<T> {
        /**
         * 构造函数
         *
         * @param item 对象
         */
        TableRowItem(T item) {
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
