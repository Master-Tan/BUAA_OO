package com.oocourse.uml1.interact.exceptions;

/**
 * 参数个数异常
 */
public abstract class ArgumentCountException extends InputArgumentException {
    private final int expectedCount;
    private final int actualCount;

    /**
     * 构造函数
     *
     * @param message       异常信息
     * @param expectedCount 期望参数个数
     * @param actualCount   实际参数个数
     */
    ArgumentCountException(String message, int expectedCount, int actualCount) {
        super(message);
        this.expectedCount = expectedCount;
        this.actualCount = actualCount;
    }

    /**
     * 获取期望参数个数
     *
     * @return 期望参数个数
     */
    public int getExpectedCount() {
        return expectedCount;
    }

    /**
     * 获取实际参数个数
     *
     * @return 实际参数个数
     */
    public int getActualCount() {
        return actualCount;
    }
}
