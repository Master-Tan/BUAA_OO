package com.oocourse.uml2.utils.common;

/**
 * 带异常的Runnable
 *
 * @param <E> 异常类型
 */
public interface RunnableWithException<E extends Exception> {
    /**
     * 运行
     *
     * @throws E 异常类型
     */
    void run() throws E;
}
