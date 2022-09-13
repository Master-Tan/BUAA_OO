package main;

import main.myumlstatemachine.MyAllState;
import main.myumlstatemachine.MyEvent;
import main.myumlstatemachine.MyFinalState;
import main.myumlstatemachine.MyPseudostate;
import main.myumlstatemachine.MyRegion;
import main.myumlstatemachine.MyStateMachine;
import main.myumlstatemachine.MyTransition;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

public class MyUmlStateMachineParser {

    private HashMap<String, MyStateMachine> myStateMachines;
    private HashMap<String, MyRegion> myRegions;
    private HashMap<String, MyTransition> myTransitions;
    private HashMap<String, Integer> stateMachineNames;
    private HashMap<String, String> stateMachineNameToId;
    private HashMap<String, MyAllState> myAllStates;

    private HashMap<String, Boolean> stateMachineExist = new HashMap<>();
    private HashMap<String, Boolean> stateMachineRepeat = new HashMap<>();
    private HashMap<String, Integer> stateCount = new HashMap<>();
    private HashMap<String, HashMap<String, Boolean>> stateExist = new HashMap<>();
    private HashMap<String, HashMap<String, Boolean>> stateRepeat = new HashMap<>();
    private HashMap<String, HashMap<String, Boolean>> stateIsCriticalPoint = new HashMap<>();
    // private HashMap<String, HashMap<String, HashMap<String, Boolean>>> transitionExist =
    //        new HashMap<>();
    // private HashMap<String, HashMap<String, HashMap<String, List<String>>>> transitionTrigger =
    //        new HashMap<>();

    public MyUmlStateMachineParser(HashMap<String, MyStateMachine> myStateMachines,
                                   HashMap<String, MyRegion> myRegions,
                                   HashMap<String, MyTransition> myTransitions,
                                   HashMap<String, Integer> stateMachineNames,
                                   HashMap<String, String> stateMachineNameToId,
                                   HashMap<String, MyAllState> myAllStates) {

        this.myStateMachines = myStateMachines;
        this.myRegions = myRegions;
        this.myTransitions = myTransitions;
        this.stateMachineNames = stateMachineNames;
        this.stateMachineNameToId = stateMachineNameToId;
        this.myAllStates = myAllStates;

    }

    public boolean isStateMachineExist(String interactionName) {
        if (stateMachineExist.containsKey(interactionName)) {
            return stateMachineExist.get(interactionName);
        } else {
            stateMachineExist.put(interactionName, stateMachineNames.containsKey(interactionName));
            return stateMachineNames.containsKey(interactionName);
        }
    }

    public boolean isStateMachineRepeat(String stateMachineName) {
        if (stateMachineRepeat.containsKey(stateMachineName)) {
            return stateMachineRepeat.get(stateMachineName);
        } else {
            if (stateMachineNames.containsKey(stateMachineName)) {
                if (stateMachineNames.get(stateMachineName) > 1) {
                    stateMachineRepeat.put(stateMachineName, true);
                    return true;
                }
            }
            stateMachineRepeat.put(stateMachineName, false);
            return false;
        }
    }

    public int getStateCount(String stateMachineName) {
        if (stateCount.containsKey(stateMachineName)) {
            return stateCount.get(stateMachineName);
        } else {
            MyStateMachine myStateMachine =
                    myStateMachines.get(stateMachineNameToId.get(stateMachineName));
            int count;
            count = 0;
            for (MyRegion myRegion : myStateMachine.getRegions().values()) {
                count += myRegion.getFinalStates().size();
                count += myRegion.getPseudostates().size();
                count += myRegion.getStates().size();
            }
            stateCount.put(stateMachineName, count);
            return count;
        }
    }

    public boolean isStateExist(String stateMachineName, String stateName) {
        if (stateExist.containsKey(stateMachineName)) {
            if (stateExist.get(stateMachineName).containsKey(stateName)) {
                return stateExist.get(stateMachineName).get(stateName);
            } else {
                MyStateMachine myStateMachine =
                        myStateMachines.get(stateMachineNameToId.get(stateMachineName));
                for (MyRegion region : myStateMachine.getRegions().values()) {
                    for (MyAllState state : region.getAllStates().values()) {
                        if (stateName.equals(state.getName())) {
                            stateExist.get(stateMachineName).put(stateName, true);
                            return true;
                        }
                    }
                }
                stateExist.get(stateMachineName).put(stateName, false);
                return false;
            }
        } else {
            MyStateMachine myStateMachine =
                    myStateMachines.get(stateMachineNameToId.get(stateMachineName));
            for (MyRegion region : myStateMachine.getRegions().values()) {
                for (MyAllState state : region.getAllStates().values()) {
                    if (stateName.equals(state.getName())) {
                        HashMap<String, Boolean> hashMap = new HashMap<>();
                        hashMap.put(stateName, true);
                        stateExist.put(stateMachineName, hashMap);
                        return true;
                    }
                }
            }
            HashMap<String, Boolean> hashMap = new HashMap<>();
            hashMap.put(stateName, false);
            stateExist.put(stateMachineName, hashMap);
            return false;
        }
    }

    public boolean isStateRepeat(String stateMachineName, String stateName) {
        if (stateRepeat.containsKey(stateMachineName)) {
            if (stateRepeat.get(stateMachineName).containsKey(stateName)) {
                return stateRepeat.get(stateMachineName).get(stateName);
            } else {
                int count = 0;
                MyStateMachine myStateMachine =
                        myStateMachines.get(stateMachineNameToId.get(stateMachineName));
                for (MyRegion region : myStateMachine.getRegions().values()) {
                    for (MyAllState state : region.getAllStates().values()) {
                        if (stateName.equals(state.getName())) {
                            count++;
                        }
                    }
                }
                if (count >= 2) {
                    stateRepeat.get(stateMachineName).put(stateName, true);
                    return true;
                }
                stateRepeat.get(stateMachineName).put(stateName, false);
                return false;
            }
        } else {
            int count = 0;
            MyStateMachine myStateMachine =
                    myStateMachines.get(stateMachineNameToId.get(stateMachineName));
            for (MyRegion region : myStateMachine.getRegions().values()) {
                for (MyAllState state : region.getAllStates().values()) {
                    if (stateName.equals(state.getName())) {
                        count++;
                    }
                }
            }
            if (count >= 2) {
                HashMap<String, Boolean> hashMap = new HashMap<>();
                hashMap.put(stateName, true);
                stateRepeat.put(stateMachineName, hashMap);
                return true;
            }
            HashMap<String, Boolean> hashMap = new HashMap<>();
            hashMap.put(stateName, false);
            stateRepeat.put(stateMachineName, hashMap);
            return false;
        }
    }

    public boolean getStateIsCriticalPoint(String stateMachineName, String stateName) {
        if (stateIsCriticalPoint.containsKey(stateMachineName)) {
            if (stateIsCriticalPoint.get(stateMachineName).containsKey(stateName)) {
                return stateIsCriticalPoint.get(stateMachineName).get(stateName);
            } else {
                MyStateMachine myStateMachine =
                        myStateMachines.get(stateMachineNameToId.get(stateMachineName));
                MyAllState myState = null;
                MyAllState initState = null;
                for (MyRegion region : myStateMachine.getRegions().values()) {
                    for (MyAllState state : region.getAllStates().values()) {
                        if (state instanceof MyPseudostate) {
                            initState = state;
                        }
                        if (stateName.equals(state.getName())) {
                            myState = state;
                        }
                    }
                }
                if (bfsFinal(initState)) {
                    stateIsCriticalPoint.get(stateMachineName).put(stateName, false);
                    return false;
                }
                // BFS
                stateIsCriticalPoint.get(stateMachineName).put(stateName, bfs(initState, myState));
                return stateIsCriticalPoint.get(stateMachineName).get(stateName);
            }
        } else {
            MyStateMachine myStateMachine =
                    myStateMachines.get(stateMachineNameToId.get(stateMachineName));
            MyAllState myState = null;
            MyAllState initState = null;
            for (MyRegion region : myStateMachine.getRegions().values()) {
                for (MyAllState state : region.getAllStates().values()) {
                    if (state instanceof MyPseudostate) {
                        initState = state;
                    }
                    if (stateName.equals(state.getName())) {
                        myState = state;
                    }
                }
            }
            if (bfsFinal(initState)) {
                HashMap<String, Boolean> hashMap = new HashMap<>();
                hashMap.put(stateName, false);
                stateIsCriticalPoint.put(stateMachineName, hashMap);
                return false;
            }
            // BFS
            HashMap<String, Boolean> hashMap = new HashMap<>();
            hashMap.put(stateName, bfs(initState, myState));
            stateIsCriticalPoint.put(stateMachineName, hashMap);
            return hashMap.get(stateName);
        }
    }

    private boolean bfsFinal(MyAllState initState) {
        ArrayList<MyAllState> bfsState = new ArrayList<>();
        bfsState.add(initState);
        int front = 0;
        int end = 0;
        HashSet<String> pass = new HashSet<>();
        while (front <= end) {
            MyAllState thisState = bfsState.get(front);
            pass.add(thisState.getId());
            if (thisState instanceof MyFinalState) {
                return false;
            }
            for (MyAllState myAllState : thisState.getNextStates().values()) {
                if (pass.contains(myAllState.getId())) {
                    continue;
                }
                bfsState.add(myAllState);
                end++;
            }
            front++;
        }
        return true;
    }

    private boolean bfs(MyAllState initState, MyAllState myState) {
        ArrayList<MyAllState> bfsState = new ArrayList<>();
        bfsState.add(initState);
        int front = 0;
        int end = 0;
        HashSet<String> pass = new HashSet<>();
        while (front <= end) {
            MyAllState thisState = bfsState.get(front);
            pass.add(thisState.getId());
            if (thisState instanceof MyFinalState) {
                return false;
            }
            for (MyAllState myAllState : thisState.getNextStates().values()) {
                if (myAllState.getId().equals(myState.getId())) {
                    continue;
                }
                if (pass.contains(myAllState.getId())) {
                    continue;
                }
                bfsState.add(myAllState);
                end++;
            }
            front++;
        }
        return true;
    }

    public boolean isTransitionExist(String stateMachineName,
                                     String sourceStateName, String targetStateName) {
        MyStateMachine myStateMachine =
                myStateMachines.get(stateMachineNameToId.get(stateMachineName));
        MyAllState sourceState = null;
        MyAllState targetState = null;
        for (MyRegion myRegion : myStateMachine.getRegions().values()) {
            for (MyAllState myAllState : myRegion.getAllStates().values()) {
                if (sourceStateName.equals(myAllState.getName())) {
                    sourceState = myAllState;
                }
                if (targetStateName.equals(myAllState.getName())) {
                    targetState = myAllState;
                }
            }
        }
        for (MyTransition myTransition : myTransitions.values()) {
            if (myTransition.getSourse().equals(sourceState.getId()) &&
                    myTransition.getTarget().equals(targetState.getId())) {
                return true;
            }
        }
        return false;
    }

    public List<String> getTransitionTrigger(String stateMachineName,
                                             String sourceStateName, String targetStateName) {
        List<String> list = new ArrayList<>();
        MyStateMachine myStateMachine =
                myStateMachines.get(stateMachineNameToId.get(stateMachineName));
        MyAllState sourceState = null;
        MyAllState targetState = null;
        for (MyRegion myRegion : myStateMachine.getRegions().values()) {
            for (MyAllState myAllState : myRegion.getAllStates().values()) {
                if (sourceStateName.equals(myAllState.getName())) {
                    sourceState = myAllState;
                }
                if (targetStateName.equals(myAllState.getName())) {
                    targetState = myAllState;
                }
            }
        }
        for (MyTransition myTransition : myTransitions.values()) {
            if (myTransition.getSourse().equals(sourceState.getId()) &&
                    myTransition.getTarget().equals(targetState.getId())) {
                for (MyEvent myEvent : myTransition.getEvents().values()) {
                    list.add(myEvent.getName());
                }
            }
        }
        return list;
    }

}
