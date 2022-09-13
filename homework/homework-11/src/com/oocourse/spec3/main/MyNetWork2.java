package com.oocourse.spec3.main;

import com.oocourse.spec3.exceptions.MessageIdNotFoundException;
import com.oocourse.spec3.exceptions.MyMessageIdNotFoundException;
import com.oocourse.spec3.exceptions.PersonIdNotFoundException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class MyNetWork2 {

    public static int deleteColdEmoji(Network network, ArrayList<Integer> emojiIdList,
                                      ArrayList<Integer> emojiHeatList,
                                      ArrayList<Message> messages, int limit) {
        ArrayList<Integer> deleteId = new ArrayList<>();
        for (int i = 0; i < emojiIdList.size(); i++) {
            if (emojiHeatList.get(i) < limit) {
                deleteId.add(i);
            }
        }
        for (int i = deleteId.size() - 1; i >= 0; i--) {
            int id = deleteId.get(i);
            emojiIdList.remove(id);
            emojiHeatList.remove(id);
        }
        deleteId.clear();
        for (int i = 0; i < messages.size(); i++) {
            if (messages.get(i) instanceof EmojiMessage) {
                if (!network.containsEmojiId(((EmojiMessage) messages.get(i)).getEmojiId())) {
                    deleteId.add(i);
                }
            }
        }
        for (int i = deleteId.size() - 1; i >= 0; i--) {
            int id = deleteId.get(i);
            messages.remove(id);
        }
        return emojiIdList.size();
    }

    public static int sendIndirectMessage(
            Network network, ArrayList<Person> people, HashMap<Person, Integer> totalPath,
            ArrayList<Integer> emojiIdList, ArrayList<Integer> emojiHeatList,
            ArrayList<Message> messages, HashMap<Person, HashSet<Person>> graph,
            int id) throws MessageIdNotFoundException {
        HashMap<Integer, Boolean> isGet;
        isGet = new HashMap<>();
        if (!network.containsMessage(id) ||
                (network.containsMessage(id) && network.getMessage(id).getType() == 1)) {
            throw new MyMessageIdNotFoundException(id);
        }
        try {
            if (network.containsMessage(id) && network.getMessage(id).getType() == 0 &&
                    !network.isCircle(network.getMessage(id).getPerson1().getId(),
                            network.getMessage(id).getPerson2().getId())) {
                return -1;
            }
        } catch (PersonIdNotFoundException e) {
            ;
        }
        Message message = network.getMessage(id);
        Person person1 = message.getPerson1();
        Person person2;
        person2 = message.getPerson2();
        totalPath.put(person1, 0);
        isGet.put(person1.getId(), true);
        Person pastAddPerson;
        pastAddPerson = person1;
        MinHeap minHeap = new MinHeap();
        for (int i = 0; i < people.size(); i++) {
            if (!people.get(i).equals(person1)) {
                isGet.put(people.get(i).getId(), false);
            }
            if (people.get(i).isLinked(person1) && !people.get(i).equals(person1)) {
                minHeap.add(people.get(i), people.get(i).queryValue(person1));
            }
        }
        while (!pastAddPerson.equals(person2)) {
            int dist = minHeap.getDist();
            Person person = minHeap.get();
            while (isGet.get(person.getId())) {
                dist = minHeap.getDist();
                person = minHeap.get();
            }
            isGet.put(person.getId(), true);
            totalPath.put(person, dist);
            for (Person peo : graph.get(person)) {
                if (!totalPath.containsKey(peo)) {
                    minHeap.add(peo,
                            peo.queryValue(person) + totalPath.get(person));
                    totalPath.put(peo,
                            peo.queryValue(person) + totalPath.get(person));
                } else if (totalPath.get(peo) >
                        peo.queryValue(person) + totalPath.get(person)) {
                    minHeap.add(peo,
                            peo.queryValue(person) + totalPath.get(person));
                }
            }
            pastAddPerson = person;
        }

        add(person1, person2, message, emojiHeatList, emojiIdList, network, messages, id);

        return totalPath.get(person2);
    }

    private static void add(Person person1, Person person2, Message message,
                            ArrayList<Integer> emojiHeatList, ArrayList<Integer> emojiIdList,
                            Network network, ArrayList<Message> messages, int id) {
        person1.addSocialValue(message.getSocialValue());
        person2.addSocialValue(message.getSocialValue());
        if (message instanceof RedEnvelopeMessage) {
            person1.addMoney(-1 * ((RedEnvelopeMessage) message).getMoney());
            person2.addMoney(((RedEnvelopeMessage) message).getMoney());
        }

        if (message instanceof EmojiMessage) {
            for (int i = 0; i < emojiIdList.size(); i++) {
                if (((EmojiMessage) message).getEmojiId() == emojiIdList.get(i)) {
                    emojiHeatList.set(i, emojiHeatList.get(i) + 1);
                }
            }
        }
        ((MyPerson) person2).addMessage(0, network.getMessage(id));
        messages.remove(network.getMessage(id));
    }

}
