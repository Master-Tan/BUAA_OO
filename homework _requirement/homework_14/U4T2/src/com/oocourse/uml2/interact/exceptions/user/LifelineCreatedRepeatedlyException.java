package com.oocourse.uml2.interact.exceptions.user;

/**
 * 生命线被重复创建异常
 */
public class LifelineCreatedRepeatedlyException extends LifelineException {
    /**
     * 构造函数
     *
     * @param interactionName 交互名称
     * @param lifelineName    生命线名称
     */
    public LifelineCreatedRepeatedlyException(String interactionName, String lifelineName) {
        super(String.format("Failed, lifeline \"%s\" in umlinteraction \"%s\" is created repeatedly.",
                lifelineName, interactionName), interactionName, lifelineName);
    }
}
