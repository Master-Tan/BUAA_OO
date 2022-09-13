package com.oocourse.uml2.interact.exceptions.user;

/**
 * 生命线异常
 */
public class LifelineException extends InteractionException {
    private final String lifelineName;

    /**
     * 构造函数
     *
     * @param message         消息
     * @param interactionName 交互名称
     * @param lifelineName    生命线名称
     */
    public LifelineException(String message, String interactionName, String lifelineName) {
        super(message, interactionName);
        this.lifelineName = lifelineName;
    }

    /**
     * 获取生命线名称
     *
     * @return 生命线名称
     */
    public String getLifelineName() {
        return lifelineName;
    }
}
