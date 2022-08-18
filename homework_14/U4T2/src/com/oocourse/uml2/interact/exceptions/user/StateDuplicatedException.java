package com.oocourse.uml2.interact.exceptions.user;

/**
 * 状态重复异常
 */
public class StateDuplicatedException extends StateException {
    /**
     * 构造函数
     *
     * @param stateMachineName 状态机名称
     * @param stateName        状态名称
     */
    public StateDuplicatedException(String stateMachineName, String stateName) {
        super(String.format("Failed, duplicated state \"%s\" in statemachine \"%s\".",
                stateName, stateMachineName), stateMachineName, stateName);
    }
}
