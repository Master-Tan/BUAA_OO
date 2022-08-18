package com.oocourse.uml2.interact.exceptions.user;

/**
 * 状态机未找到异常
 */
public class StateMachineNotFoundException extends StateMachineException {
    /**
     * 构造函数
     *
     * @param stateMachineName 状态机名称
     */
    public StateMachineNotFoundException(String stateMachineName) {
        super(
                String.format("Failed, statemachine \"%s\" not found.", stateMachineName),
                stateMachineName
        );
    }
}
