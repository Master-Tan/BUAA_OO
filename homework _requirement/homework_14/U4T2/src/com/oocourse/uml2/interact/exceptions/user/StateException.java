package com.oocourse.uml2.interact.exceptions.user;

/**
 * 状态机状态异常
 */
public abstract class StateException extends StateMachineException {
    private final String stateName;

    /**
     * 构造函数
     *
     * @param message          异常信息
     * @param stateMachineName 状态机名称
     * @param stateName        状态名称
     */
    public StateException(String message, String stateMachineName, String stateName) {
        super(message, stateMachineName);
        this.stateName = stateName;
    }

    /**
     * 获取状态
     *
     * @return 状态
     */
    public String getStateName() {
        return stateName;
    }
}
