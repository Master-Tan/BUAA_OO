package com.oocourse.uml2.interact.format;

import com.oocourse.uml2.interact.exceptions.user.StateDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.StateMachineNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.StateNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.TransitionNotFoundException;

import java.util.List;

/**
 * UML状态图交互
 */
public interface UmlStateChartApi {
    /**
     * 获取状态机的状态数
     * 指令：STATE_COUNT
     *
     * @param stateMachineName 状态机名称
     * @return 状态数
     * @throws StateMachineNotFoundException   状态机未找到
     * @throws StateMachineDuplicatedException 状态机存在重名
     */
    int getStateCount(String stateMachineName)
            throws StateMachineNotFoundException, StateMachineDuplicatedException;

    /**
     * 判断其是否是关键状态
     * 指令：STATE_IS_CRITICAL_POINT
     *
     * @param stateMachineName 状态机名称
     * @param stateName        状态名称
     * @return 是否是关键状态
     * @throws StateMachineNotFoundException   状态机未找到
     * @throws StateMachineDuplicatedException 状态机存在重名
     * @throws StateNotFoundException          状态未找到
     * @throws StateDuplicatedException        状态存在重名
     */
    boolean getStateIsCriticalPoint(String stateMachineName, String stateName)
            throws StateMachineNotFoundException, StateMachineDuplicatedException,
            StateNotFoundException, StateDuplicatedException;

    /**
     * 获取引起状态迁移的触发事件
     * 指令：TRANSITION_TRIGGER
     *
     * @param stateMachineName 状态机名称
     * @param sourceStateName  状态迁移源状态名称
     * @param targetStateName  状态迁移目标状态名称
     * @return 引起状态迁移的触发事件列表
     * @throws StateMachineNotFoundException   状态机未找到
     * @throws StateMachineDuplicatedException 状态机存在重名
     * @throws StateNotFoundException          状态未找到
     * @throws StateDuplicatedException        状态存在重名
     * @throws TransitionNotFoundException     不存在从源状态到目标状态的状态迁移
     */
    List<String> getTransitionTrigger(
        String stateMachineName, String sourceStateName, String targetStateName
    )
            throws StateMachineNotFoundException, StateMachineDuplicatedException,
            StateNotFoundException, StateDuplicatedException,
            TransitionNotFoundException;
}
