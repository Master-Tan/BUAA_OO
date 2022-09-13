package com.oocourse.uml2.interact.exceptions.user;

/**
 * 交互未找到异常
 */
public class InteractionNotFoundException extends InteractionException {
    /**
     * 构造函数
     *
     * @param interactionName 交互名称
     */
    public InteractionNotFoundException(String interactionName) {
        super(String.format("Failed, umlinteraction \"%s\" not found.",
                interactionName), interactionName);
    }
}
