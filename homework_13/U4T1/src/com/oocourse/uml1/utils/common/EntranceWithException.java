package com.oocourse.uml1.utils.common;

/**
 * 带异常入口点
 *
 * @param <E> 异常类型
 */
public interface EntranceWithException<E extends Exception> {
    /**
     * 构造函数
     *
     * @param args 命令行参数
     * @throws E 抛出的异常
     */
    void run(String[] args) throws E;
}
