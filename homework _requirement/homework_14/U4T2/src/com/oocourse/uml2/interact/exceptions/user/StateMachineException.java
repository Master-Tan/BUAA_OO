package com.oocourse.uml2.interact.exceptions.user;

/**
 * 状态机异常
 */
public abstract class StateMachineException extends UserProcessException {
    private final String stateMachineName;

    /**
     * 构造函数
     *
     * @param message          异常消息
     * @param stateMachineName 状态机名称
     */
    public StateMachineException(String message, String stateMachineName) {
        super(message);
        this.stateMachineName = stateMachineName;
    }

    /**
     * 获取状态机
     *
     * @return 状态机
     */
    public String getStateMachineName() {
        return stateMachineName;
    }
}
