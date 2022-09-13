package com.oocourse.uml2.interact.exceptions.user;

/**
 * 生命线未找到异常
 */
public class LifelineNotFoundException extends LifelineException {
    /**
     * 构造函数
     *
     * @param interactionName 交互名称
     * @param lifelineName    生命线名称
     */
    public LifelineNotFoundException(String interactionName, String lifelineName) {
        super(String.format("Failed, lifeline \"%s\" in umlinteraction \"%s\" not found.",
                lifelineName, interactionName), interactionName, lifelineName);
    }
}
