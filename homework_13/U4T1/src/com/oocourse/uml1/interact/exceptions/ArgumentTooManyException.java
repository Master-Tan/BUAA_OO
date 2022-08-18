package com.oocourse.uml1.interact.exceptions;

/**
 * 参数个数过多异常
 */
public class ArgumentTooManyException extends ArgumentCountException {
    /**
     * 构造函数
     *
     * @param expectedCount 期望参数个数
     * @param actualCount   实际参数个数
     */
    public ArgumentTooManyException(int expectedCount, int actualCount) {
        super(String.format("Argument too many, %s expected but %s found.",
                expectedCount, actualCount), expectedCount, actualCount);
    }
}
