package com.oocourse.uml2.interact.exceptions.user;

/**
 * 交互信息异常
 */
public abstract class InteractionException extends UserProcessException {
    private final String interactionName;

    /**
     * 构造函数
     *
     * @param message         异常信息
     * @param interactionName 交互名称
     */
    public InteractionException(String message, String interactionName) {
        super(message);
        this.interactionName = interactionName;
    }

    /**
     * 获取交互名称
     *
     * @return 交互名称
     */
    public String getInteractionName() {
        return interactionName;
    }
}
