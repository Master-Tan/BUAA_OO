package com.oocourse.uml2.interact.exceptions.user;

/**
 * 状态机重名异常
 */
public class StateMachineDuplicatedException extends StateMachineException {
    /**
     * 构造函数
     *
     * @param stateMachineName 状态机名称
     */
    public StateMachineDuplicatedException(String stateMachineName) {
        super(
                String.format("Failed, duplicated statemachine \"%s\".", stateMachineName),
                stateMachineName
        );
    }
}
