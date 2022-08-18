package com.oocourse.uml2.interact.exceptions.user;

/**
 * 生命线重名异常
 */
public class LifelineDuplicatedException extends LifelineException {
    /**
     * 构造函数
     *
     * @param interactionName 交互名称
     * @param lifelineName    生命线名称
     */
    public LifelineDuplicatedException(String interactionName, String lifelineName) {
        super(String.format("Failed, duplicated lifeline \"%s\" in umlinteraction \"%s\".",
                lifelineName, interactionName), interactionName, lifelineName);
    }
}
