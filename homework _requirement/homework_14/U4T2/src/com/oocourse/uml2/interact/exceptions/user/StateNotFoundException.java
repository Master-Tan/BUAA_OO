package com.oocourse.uml2.interact.exceptions.user;

/**
 * 状态未找到异常
 */
public class StateNotFoundException extends StateException {

    /**
     * 构造函数
     *
     * @param stateMachineName 状态机名称
     * @param stateName        状态名称
     */
    public StateNotFoundException(String stateMachineName, String stateName) {
        super(String.format("Failed, state \"%s\" in statemachine \"%s\" not found.",
                stateName, stateMachineName), stateMachineName, stateName);
    }
}
