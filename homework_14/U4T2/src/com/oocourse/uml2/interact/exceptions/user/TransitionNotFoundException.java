package com.oocourse.uml2.interact.exceptions.user;

public class TransitionNotFoundException extends StateMachineException {
    /**
     * 构造函数
     *
     * @param stateMachineName 状态机名称
     * @param sourceStateName 状态迁移源状态名称
     * @param targetStateName 状态迁移目标状态名称
     */
    public TransitionNotFoundException(String stateMachineName, String sourceStateName, String targetStateName) {
        super(
            String.format(
                "Failed, transition from state \"%s\" to state \"%s\" in statemachine \"%s\" not found.",
                sourceStateName, targetStateName, stateMachineName),
            stateMachineName
        );
    }
}
