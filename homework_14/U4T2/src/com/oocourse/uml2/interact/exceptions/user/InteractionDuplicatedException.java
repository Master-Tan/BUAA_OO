package com.oocourse.uml2.interact.exceptions.user;

/**
 * 交互重复异常
 */
public class InteractionDuplicatedException extends InteractionException {
    /**
     * 构造函数
     *
     * @param interactionName 交互名称
     */
    public InteractionDuplicatedException(String interactionName) {
        super(String.format("Failed, duplicated umlinteraction \"%s\".",
                interactionName), interactionName);
    }
}
