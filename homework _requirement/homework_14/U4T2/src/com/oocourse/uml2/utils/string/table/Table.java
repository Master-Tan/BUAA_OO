package com.oocourse.uml2.utils.string.table;

import com.oocourse.uml2.utils.string.AlignedString;
import com.oocourse.uml2.utils.string.StringUtils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * 表格
 */
public class Table {
    static final String ROW_PREFIX = "| ";
    static final String ROW_DELIMITER = " | ";
    static final String ROW_SUFFIX = " |";
    private static final String LINE_UNIT = "-";
    private static final String LINE_PREFIX = "+";
    private static final String LINE_DELIMITER = "+";
    private static final String LINE_SUFFIX = "+";

    private final TableHeader header;
    private final List<TableRow> rows;

    /**
     * 构造函数
     *
     * @param headerItems 表头各项
     */
    public Table(List<Object> headerItems) {
        this.header = new TableHeader(headerItems);
        this.rows = new ArrayList<>();
    }

    /**
     * 构造函数
     *
     * @param headerItems 表头各项
     */
    public Table(Object... headerItems) {
        this(Arrays.asList(headerItems));
    }

    /**
     * 清空表格
     */
    public void clear() {
        this.rows.clear();
    }

    /**
     * 添加行
     *
     * @param rowItems 行各项
     */
    public void addRow(List<Object> rowItems) {
        List<Object> items = IntStream.range(0, this.header.size()).boxed()
                .map(i -> ((i < rowItems.size()) ? rowItems.get(i) : null))
                .collect(Collectors.toList());
        this.rows.add(new TableRow(items));
    }

    /**
     * 添加行
     *
     * @param rowItems 行各项
     */
    public void addRow(Object... rowItems) {
        this.addRow(Arrays.asList(rowItems));
    }

    /**
     * 获取各列宽度
     *
     * @return 各列宽度
     */
    private List<Integer> getColumnLength() {
        List<Integer> result = new ArrayList<>();
        for (int columnIndex = 0; columnIndex < this.header.size(); columnIndex++) {
            int maxLength = this.header.getItem(columnIndex).toString().length();
            for (TableRow row : rows) {
                maxLength = Math.max(maxLength, row.getItem(columnIndex).toString().length());
            }
            result.add(maxLength);
        }
        return result;
    }

    /**
     * 获取字符串形式
     *
     * @return 字符串形式
     */
    @Override
    public String toString() {
        List<Integer> columnLength = getColumnLength();
        String line = columnLength.stream()
                .map(length -> Collections.nCopies(length + 2, LINE_UNIT)
                        .stream().collect(Collectors.joining()))
                .collect(Collectors.joining(LINE_DELIMITER, LINE_PREFIX, LINE_SUFFIX));

        StringBuilder builder = new StringBuilder();
        Runnable addLine = () -> {
            builder.append(line);
            builder.append(StringUtils.LINE_SEPARATOR);
        };
        BiConsumer<TableAbstractRow, AlignedString.AlignMode> addRow
                = (TableAbstractRow row, AlignedString.AlignMode alignMode) -> {
            builder.append(IntStream.range(0, row.size()).boxed()
                    .map(index -> AlignedString.getAlignedString(
                            row.getItem(index), columnLength.get(index), alignMode))
                    .map(AlignedString::toString)
                    .collect(Collectors.joining(ROW_DELIMITER, ROW_PREFIX, ROW_SUFFIX)));
            builder.append(StringUtils.LINE_SEPARATOR);
        };

        addLine.run();
        addRow.accept(this.header, AlignedString.AlignMode.MIDDLE);
        addLine.run();
        this.rows.forEach(row -> addRow.accept(row, AlignedString.AlignMode.LEFT));
        addLine.run();
        return builder.toString();
    }

    /**
     * 相等性判定
     *
     * @param o 对象
     * @return 是否相等
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Table table = (Table) o;
        return Objects.equals(header, table.header) &&
                Objects.equals(rows, table.rows);
    }

    /**
     * 获取哈希值
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Objects.hash(header, rows);
    }
}
