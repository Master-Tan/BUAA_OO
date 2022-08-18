package com.oocourse.uml2.interact.common;

import java.util.Objects;

/**
 * 输出信息
 */
public class OutputInformation {
    private final String message;

    /**
     * 构造函数
     *
     * @param message 文本信息
     */
    public OutputInformation(String message) {
        this.message = message;
    }

    /**
     * 获取信息
     *
     * @return 信息
     */
    public String getMessage() {
        return message;
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
        OutputInformation that = (OutputInformation) o;
        return Objects.equals(message, that.message);
    }

    /**
     * 哈希值求解
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Objects.hash(message);
    }

    /**
     * 转为字符串形式
     *
     * @return 字符串形式
     */
    @Override
    public String toString() {
        return this.getMessage();
    }
}
