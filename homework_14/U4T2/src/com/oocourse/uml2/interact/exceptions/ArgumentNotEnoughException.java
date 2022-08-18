package com.oocourse.uml2.interact.exceptions;

/**
 * 参数个数过少异常
 */
public class ArgumentNotEnoughException extends ArgumentCountException {
    /**
     * 构造函数
     *
     * @param expectedCount 期望参数个数
     * @param actualCount   实际参数个数
     */
    public ArgumentNotEnoughException(int expectedCount, int actualCount) {
        super(String.format("Argument not enough, %s expected but %s found.",
                expectedCount, actualCount), expectedCount, actualCount);
    }
}
