package main;

import com.oocourse.uml3.interact.common.Pair;
import com.oocourse.uml3.models.common.MessageSort;
import com.oocourse.uml3.models.elements.UmlLifeline;
import main.myumlcollaboration.MyCollaboration;
import main.myumlcollaboration.MyEndPoint;
import main.myumlcollaboration.MyInteraction;
import main.myumlcollaboration.MyLifeline;
import main.myumlcollaboration.MyMessage;

import java.util.HashMap;

public class MyUmlCollaborationParser {

    private HashMap<String, MyCollaboration> myCollaborations;
    private HashMap<String, MyInteraction> myInteractions;
    private HashMap<String, Integer> interactionNames;
    private HashMap<String, String> interactionNameToId;
    private HashMap<String, MyLifeline> myLifelines;
    private HashMap<String, UmlLifeline> myUmlLifelines;
    private HashMap<String, MyEndPoint> myEndPoints;

    private HashMap<String, Integer> participantCount = new HashMap<>();
    private HashMap<String, HashMap<String, Boolean>> lifelineExist = new HashMap<>();
    private HashMap<String, HashMap<String, Boolean>> lifelineRepeat = new HashMap<>();
    private HashMap<String, HashMap<String, Boolean>> lifelineCreateExist = new HashMap<>();
    private HashMap<String, HashMap<String, Boolean>> lifelineCreateRepeat = new HashMap<>();
    private HashMap<String, HashMap<String, UmlLifeline>> participantCreator = new HashMap<>();
    private HashMap<String, HashMap<String, Pair<Integer, Integer>>> participantLostAndFound =
            new HashMap<>();

    public MyUmlCollaborationParser(HashMap<String, MyCollaboration> myCollaborations,
                                    HashMap<String, MyInteraction> myInteractions,
                                    HashMap<String, Integer> interactionNames,
                                    HashMap<String, String> interactionNameToId,
                                    HashMap<String, MyLifeline> myLifelines,
                                    HashMap<String, UmlLifeline> myUmlLifelines,
                                    HashMap<String, MyEndPoint> myEndPoints) {

        this.myCollaborations = myCollaborations;
        this.myInteractions = myInteractions;
        this.interactionNames = interactionNames;
        this.interactionNameToId = interactionNameToId;
        this.myLifelines = myLifelines;
        this.myUmlLifelines = myUmlLifelines;
        this.myEndPoints = myEndPoints;

    }

    public boolean isInteractionExist(String interactionName) {
        return interactionNames.containsKey(interactionName);
    }

    public boolean isInteractionRepeat(String interactionName) {
        if (interactionNames.containsKey(interactionName)) {
            if (interactionNames.get(interactionName) > 1) {
                return true;
            }
        }
        return false;
    }

    public int getParticipantCount(String interactionName) {
        int count;
        if (participantCount.containsKey(interactionName)) {
            count = participantCount.get(interactionName);
        } else {
            MyInteraction myInteraction =
                    myInteractions.get(interactionNameToId.get(interactionName));
            count = myInteraction.getLifelines().size();
        }
        return count;
    }

    public boolean isLifelineExist(String interactionName, String lifelineName) {
        MyInteraction myInteraction = myInteractions.get(interactionNameToId.get(interactionName));
        if (lifelineExist.containsKey(interactionName)) {
            if (lifelineExist.get(interactionName).containsKey(lifelineName)) {
                return lifelineExist.get(interactionName).get(lifelineName);
            } else {
                for (MyLifeline myLifeline : myInteraction.getLifelines().values()) {
                    if (lifelineName.equals(myLifeline.getName())) {
                        lifelineExist.get(interactionName).put(lifelineName, true);
                        return true;
                    }
                }
                lifelineExist.get(interactionName).put(lifelineName, false);
                return false;
            }
        } else {
            for (MyLifeline myLifeline : myInteraction.getLifelines().values()) {
                if (lifelineName.equals(myLifeline.getName())) {
                    HashMap<String, Boolean> hashMap = new HashMap<>();
                    hashMap.put(lifelineName, true);
                    lifelineExist.put(interactionName, hashMap);
                    return true;
                }
            }
            HashMap<String, Boolean> hashMap = new HashMap<>();
            hashMap.put(lifelineName, false);
            lifelineExist.put(interactionName, hashMap);
            return false;
        }
    }

    public boolean isLifelineRepeat(String interactionName, String lifelineName) {
        if (lifelineRepeat.containsKey(interactionName)) {
            if (lifelineRepeat.get(interactionName).containsKey(lifelineName)) {
                return lifelineRepeat.get(interactionName).get(lifelineName);
            } else {
                int count = 0;
                MyInteraction myInteraction =
                        myInteractions.get(interactionNameToId.get(interactionName));
                for (MyLifeline myLifeline : myInteraction.getLifelines().values()) {
                    if (lifelineName.equals(myLifeline.getName())) {
                        count++;
                    }
                }
                if (count >= 2) {
                    lifelineRepeat.get(interactionName).put(lifelineName, true);
                    return true;
                }
                lifelineRepeat.get(interactionName).put(lifelineName, false);
                return false;
            }
        } else {
            int count = 0;
            MyInteraction myInteraction =
                    myInteractions.get(interactionNameToId.get(interactionName));
            for (MyLifeline myLifeline : myInteraction.getLifelines().values()) {
                if (lifelineName.equals(myLifeline.getName())) {
                    count++;
                }
            }
            if (count >= 2) {
                HashMap<String, Boolean> hashMap = new HashMap<>();
                hashMap.put(lifelineName, true);
                lifelineRepeat.put(interactionName, hashMap);
                return true;
            }
            HashMap<String, Boolean> hashMap = new HashMap<>();
            hashMap.put(lifelineName, false);
            lifelineRepeat.put(interactionName, hashMap);
            return false;
        }

    }

    public boolean isLifelineCreateExist(String interactionName, String lifelineName) {
        if (lifelineCreateExist.containsKey(interactionName)) {
            if (lifelineCreateExist.get(interactionName).containsKey(lifelineName)) {
                return lifelineCreateExist.get(interactionName).get(lifelineName);
            } else {
                MyInteraction myInteraction =
                        myInteractions.get(interactionNameToId.get(interactionName));
                MyLifeline myLifeline = null;
                for (MyLifeline lifeline : myInteraction.getLifelines().values()) {
                    if (lifelineName.equals(lifeline.getName())) {
                        myLifeline = lifeline;
                    }
                }
                for (MyMessage myMessage : myInteraction.getMessages().values()) {
                    if (myMessage.getMessageSort() == MessageSort.CREATE_MESSAGE) {
                        if (myMessage.getTarget().equals(myLifeline.getId())) {
                            lifelineCreateExist.get(interactionName).put(lifelineName, true);
                            return true;
                        }
                    }
                }
                lifelineCreateExist.get(interactionName).put(lifelineName, false);
                return false;
            }
        } else {
            MyInteraction myInteraction =
                    myInteractions.get(interactionNameToId.get(interactionName));
            MyLifeline myLifeline = null;
            for (MyLifeline lifeline : myInteraction.getLifelines().values()) {
                if (lifelineName.equals(lifeline.getName())) {
                    myLifeline = lifeline;
                }
            }
            for (MyMessage myMessage : myInteraction.getMessages().values()) {
                if (myMessage.getMessageSort() == MessageSort.CREATE_MESSAGE) {
                    if (myMessage.getTarget().equals(myLifeline.getId())) {
                        HashMap<String, Boolean> hashMap = new HashMap<>();
                        hashMap.put(lifelineName, true);
                        lifelineCreateExist.put(interactionName, hashMap);
                        return true;
                    }
                }
            }
            HashMap<String, Boolean> hashMap = new HashMap<>();
            hashMap.put(lifelineName, false);
            lifelineCreateExist.put(interactionName, hashMap);
            return false;
        }

    }

    public boolean isLifelineCreateRepeat(String interactionName, String lifelineName) {
        if (lifelineCreateRepeat.containsKey(interactionName)) {
            if (lifelineCreateRepeat.containsKey(lifelineName)) {
                return lifelineCreateRepeat.get(interactionName).get(lifelineName);
            } else {
                int count = 0;
                MyInteraction myInteraction =
                        myInteractions.get(interactionNameToId.get(interactionName));
                MyLifeline myLifeline = null;
                for (MyLifeline lifeline : myInteraction.getLifelines().values()) {
                    if (lifelineName.equals(lifeline.getName())) {
                        myLifeline = lifeline;
                    }
                }
                for (MyMessage myMessage : myInteraction.getMessages().values()) {
                    if (myMessage.getMessageSort() == MessageSort.CREATE_MESSAGE) {
                        if (myMessage.getTarget().equals(myLifeline.getId())) {
                            count++;
                        }
                    }
                }
                if (count >= 2) {
                    lifelineCreateRepeat.get(interactionName).put(lifelineName, true);
                    return true;
                }
                lifelineCreateRepeat.get(interactionName).put(lifelineName, false);
                return false;
            }
        } else {
            int count = 0;
            MyInteraction myInteraction =
                    myInteractions.get(interactionNameToId.get(interactionName));
            MyLifeline myLifeline = null;
            for (MyLifeline lifeline : myInteraction.getLifelines().values()) {
                if (lifelineName.equals(lifeline.getName())) {
                    myLifeline = lifeline;
                }
            }
            for (MyMessage myMessage : myInteraction.getMessages().values()) {
                if (myMessage.getMessageSort() == MessageSort.CREATE_MESSAGE) {
                    if (myMessage.getTarget().equals(myLifeline.getId())) {
                        count++;
                    }
                }
            }
            if (count >= 2) {
                HashMap<String, Boolean> hashMap = new HashMap<>();
                hashMap.put(lifelineName, true);
                lifelineCreateRepeat.put(interactionName, hashMap);
                return true;
            }
            HashMap<String, Boolean> hashMap = new HashMap<>();
            hashMap.put(lifelineName, false);
            lifelineCreateRepeat.put(interactionName, hashMap);
            return false;
        }

    }

    public UmlLifeline getParticipantCreator(String interactionName, String lifelineName) {
        if (participantCreator.containsKey(interactionName)) {
            if (participantCreator.containsKey(lifelineName)) {
                return participantCreator.get(interactionName).get(lifelineName);
            } else {
                MyInteraction myInteraction =
                        myInteractions.get(interactionNameToId.get(interactionName));
                MyLifeline myLifeline = null;
                for (MyLifeline lifeline : myInteraction.getLifelines().values()) {
                    if (lifelineName.equals(lifeline.getName())) {
                        myLifeline = lifeline;
                    }
                }
                for (MyMessage myMessage : myInteraction.getMessages().values()) {
                    if (myMessage.getMessageSort() == MessageSort.CREATE_MESSAGE) {
                        if (myMessage.getTarget().equals(myLifeline.getId())) {
                            participantCreator.get(interactionName).put(
                                    lifelineName, myUmlLifelines.get(myMessage.getSourse()));
                            return myUmlLifelines.get(myMessage.getSourse());
                        }
                    }
                }
                return null;
            }
        } else {
            MyInteraction myInteraction =
                    myInteractions.get(interactionNameToId.get(interactionName));
            MyLifeline myLifeline = null;
            for (MyLifeline lifeline : myInteraction.getLifelines().values()) {
                if (lifelineName.equals(lifeline.getName())) {
                    myLifeline = lifeline;
                }
            }
            for (MyMessage myMessage : myInteraction.getMessages().values()) {
                if (myMessage.getMessageSort() == MessageSort.CREATE_MESSAGE) {
                    if (myMessage.getTarget().equals(myLifeline.getId())) {
                        HashMap<String, UmlLifeline> hashMap = new HashMap<>();
                        hashMap.put(lifelineName, myUmlLifelines.get(myMessage.getSourse()));
                        participantCreator.put(interactionName, hashMap);
                        return myUmlLifelines.get(myMessage.getSourse());
                    }
                }
            }
            return null;
        }
    }

    public Pair<Integer, Integer> getParticipantLostAndFound(String interactionName,
                                                             String lifelineName) {
        if (participantLostAndFound.containsKey(interactionName)) {
            if (participantLostAndFound.containsKey(lifelineName)) {
                return participantLostAndFound.get(interactionName).get(lifelineName);
            } else {
                int foundCount = 0;
                int lostCount = 0;
                MyInteraction myInteraction =
                        myInteractions.get(interactionNameToId.get(interactionName));
                for (MyLifeline myLifeline : myInteraction.getLifelines().values()) {
                    if (lifelineName.equals(myLifeline.getName())) {
                        for (String source : myLifeline.getReceivers()) {
                            if (myEndPoints.containsKey(source)) {
                                foundCount++;
                            }
                        }
                        for (String target : myLifeline.getSenders()) {
                            if (myEndPoints.containsKey(target)) {
                                lostCount++;
                            }
                        }
                    }
                }
                participantLostAndFound.get(interactionName).put(
                        lifelineName, new Pair<>(foundCount, lostCount));
                return new Pair<>(foundCount, lostCount);
            }
        } else {
            int foundCount = 0;
            int lostCount = 0;
            MyInteraction myInteraction =
                    myInteractions.get(interactionNameToId.get(interactionName));
            for (MyLifeline myLifeline : myInteraction.getLifelines().values()) {
                if (lifelineName.equals(myLifeline.getName())) {
                    for (String source : myLifeline.getReceivers()) {
                        if (myEndPoints.containsKey(source)) {
                            foundCount++;
                        }
                    }
                    for (String target : myLifeline.getSenders()) {
                        if (myEndPoints.containsKey(target)) {
                            lostCount++;
                        }
                    }
                }
            }
            HashMap<String, Pair<Integer, Integer>> hashMap = new HashMap<>();
            hashMap.put(lifelineName, new Pair<>(foundCount, lostCount));
            participantLostAndFound.put(interactionName, hashMap);
            return new Pair<>(foundCount, lostCount);
        }

    }

}

