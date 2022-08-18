package com.oocourse.uml2.interact.exceptions.user;

/**
 * 生命线未被创建异常
 */
public class LifelineNeverCreatedException extends LifelineException {
    /**
     * 构造函数
     *
     * @param interactionName 交互名称
     * @param lifelineName    生命线名称
     */
    public LifelineNeverCreatedException(String interactionName, String lifelineName) {
        super(String.format("Failed, lifeline \"%s\" in umlinteraction \"%s\" is never created.",
                lifelineName, interactionName), interactionName, lifelineName);
    }
}
