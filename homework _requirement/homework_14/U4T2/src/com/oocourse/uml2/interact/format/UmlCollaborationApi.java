package com.oocourse.uml2.interact.format;

import com.oocourse.uml2.interact.common.Pair;
import com.oocourse.uml2.interact.exceptions.user.InteractionDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.InteractionNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.LifelineCreatedRepeatedlyException;
import com.oocourse.uml2.interact.exceptions.user.LifelineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNeverCreatedException;
import com.oocourse.uml2.interact.exceptions.user.LifelineNotFoundException;
import com.oocourse.uml2.models.elements.UmlLifeline;

/**
 * UML顺序图交互
 */
public interface UmlCollaborationApi {
    /**
     * 获取参与对象数
     * 指令：PTCP_OBJ_COUNT
     *
     * @param interactionName 交互名称
     * @return 参与对象数
     * @throws InteractionNotFoundException   交互未找到
     * @throws InteractionDuplicatedException 交互重名
     */
    int getParticipantCount(String interactionName)
            throws InteractionNotFoundException, InteractionDuplicatedException;

    /**
     * 获取对象创建者
     * 指令：PTCP_CREATOR
     *
     * @param interactionName 交互名称
     * @param lifelineName    消息名称
     * @return 对象创建者
     * @throws InteractionNotFoundException       交互未找到
     * @throws InteractionDuplicatedException     交互重名
     * @throws LifelineNotFoundException          生命线未找到
     * @throws LifelineDuplicatedException        生命线重名
     * @throws LifelineNeverCreatedException      生命线没有被创建
     * @throws LifelineCreatedRepeatedlyException 生命线多次被创建
     */
    UmlLifeline getParticipantCreator(String interactionName, String lifelineName)
            throws InteractionNotFoundException, InteractionDuplicatedException,
            LifelineNotFoundException, LifelineDuplicatedException,
            LifelineNeverCreatedException, LifelineCreatedRepeatedlyException;

    /**
     * 获取对象收到了多少个 Found 消息，发出了多少个 Lost 消息
     * 指令：PTCP_LOST_AND_FOUND
     *
     * @param interactionName 交互名称
     * @param lifelineName    消息名称
     * @return Pair(收到的FOUND消息数，发出的LOST消息数)
     * @throws InteractionNotFoundException   交互未找到
     * @throws InteractionDuplicatedException 交互重名
     * @throws LifelineNotFoundException      生命线未找到
     * @throws LifelineDuplicatedException    生命线重名
     */
    Pair<Integer, Integer> getParticipantLostAndFound(String interactionName, String lifelineName)
            throws InteractionNotFoundException, InteractionDuplicatedException,
            LifelineNotFoundException, LifelineDuplicatedException;
}
