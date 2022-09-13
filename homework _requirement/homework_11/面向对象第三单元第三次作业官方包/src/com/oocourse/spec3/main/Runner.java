package com.oocourse.spec3.main;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import com.oocourse.spec3.exceptions.EmojiIdNotFoundException;
import com.oocourse.spec3.exceptions.EqualEmojiIdException;
import com.oocourse.spec3.exceptions.EqualGroupIdException;
import com.oocourse.spec3.exceptions.EqualMessageIdException;
import com.oocourse.spec3.exceptions.EqualPersonIdException;
import com.oocourse.spec3.exceptions.EqualRelationException;
import com.oocourse.spec3.exceptions.GroupIdNotFoundException;
import com.oocourse.spec3.exceptions.MessageIdNotFoundException;
import com.oocourse.spec3.exceptions.PersonIdNotFoundException;
import com.oocourse.spec3.exceptions.RelationNotFoundException;

public class Runner {

    private String[] cmds;
    private Network network;
    private Class<? extends Person> personClass;
    private Class<? extends Network> networkClass;
    private Class<? extends Group> groupClass;
    private Class<? extends Message> messageClass;
    private Class<? extends EmojiMessage> emojiClass;
    private Class<? extends NoticeMessage> noticeClass;
    private Class<? extends RedEnvelopeMessage> redEnvelopeClass;
    private Constructor<? extends Person> personConstructor;
    private Constructor<? extends Network> networkConstructor;
    private Constructor<? extends Group> groupConstructor;
    private Constructor<? extends Message> messageConstructor0;
    private Constructor<? extends Message> messageConstructor1;
    private Constructor<? extends EmojiMessage> emojiConstructor0;
    private Constructor<? extends EmojiMessage> emojiConstructor1;
    private Constructor<? extends RedEnvelopeMessage> redEnvelopeConstructor0;
    private Constructor<? extends RedEnvelopeMessage> redEnvelopeConstructor1;
    private Constructor<? extends NoticeMessage> noticeConstructor0;
    private Constructor<? extends NoticeMessage> noticeConstructor1;
    private Scanner cin;

    public Runner(Class<? extends Person> personClass, Class<? extends Network> networkClass,
                  Class<? extends Group> groupClass, Class<? extends Message> messageClass,
                  Class<? extends EmojiMessage> emojiClass, Class<? extends NoticeMessage> noticeClass,
                  Class<? extends RedEnvelopeMessage> redEnvelopeClass) throws NoSuchMethodException, SecurityException {
        this.personClass = personClass;
        this.networkClass = networkClass;
        this.groupClass = groupClass;
        this.messageClass = messageClass;
        this.emojiClass = emojiClass;
        this.noticeClass = noticeClass;
        this.redEnvelopeClass = redEnvelopeClass;
        personConstructor = this.personClass.getConstructor(
                int.class, String.class, int.class);
        networkConstructor = this.networkClass.getConstructor();
        groupConstructor = this.groupClass.getConstructor(int.class);
        messageConstructor0 = this.messageClass.getConstructor(int.class, int.class, Person.class, Person.class);
        messageConstructor1 = this.messageClass.getConstructor(int.class, int.class, Person.class, Group.class);
        emojiConstructor0 = this.emojiClass.getConstructor(int.class, int.class, Person.class, Person.class);
        emojiConstructor1 = this.emojiClass.getConstructor(int.class, int.class, Person.class, Group.class);
        noticeConstructor0 = this.noticeClass.getConstructor(int.class, String.class, Person.class, Person.class);
        noticeConstructor1 = this.noticeClass.getConstructor(int.class, String.class, Person.class, Group.class);
        redEnvelopeConstructor0 = this.redEnvelopeClass.getConstructor(int.class, int.class, Person.class, Person.class);
        redEnvelopeConstructor1 = this.redEnvelopeClass.getConstructor(int.class, int.class, Person.class, Group.class);
        cin = new Scanner(System.in);
    }

    public void run()
            throws InstantiationException, IllegalAccessException,
            IllegalArgumentException, InvocationTargetException {
        this.network = (Network) this.networkConstructor.newInstance();
        while (cin.hasNextLine()) {
            String cmd = cin.nextLine();
            cmds = cmd.split(" ");
            if (cmds[0].equals("ap")) {
                addPerson();
            } else if (cmds[0].equals("ar")) {
                addRelation();
            } else if (cmds[0].equals("qv")) {
                queryValue();
            } else if (cmds[0].equals("qps")) {
                queryPeopleSum();
            } else if (cmds[0].equals("qci")) {
                queryCircle();
            } else if (cmds[0].equals("ag")) {
                addGroup();
            } else if (cmds[0].equals("atg")) {
                addToGroup();
            } else if (cmds[0].equals("qgps")) {
                queryGroupPeopleSum();
            } else if (cmds[0].equals("qgvs")) {
                queryGroupValueSum();
            } else if (cmds[0].equals("qgav")) {
                queryGroupAgeVar();
            } else if (cmds[0].equals("dfg")) {
                delFromGroup();
            } else if (cmds[0].equals("qbs")) {
                queryBlockSum();
            } else if (cmds[0].equals("am")) {
                addMessage();
            } else if (cmds[0].equals("sm")) {
                sendMessage();
            } else if (cmds[0].equals("qsv")) {
                querySocialValue();
            } else if (cmds[0].equals("qrm")) {
                queryReceivedMessages();
            } else if (cmds[0].equals("sim")) {
                sendIndirectMessage();
            } else if (cmds[0].equals("sei")) {
                storeEmojiId();
            } else if (cmds[0].equals("arem")) {
                addRedEnvelopeMessage();
            } else if (cmds[0].equals("anm")) {
                addNoticeMessage();
            } else if (cmds[0].equals("aem")) {
                addEmojiMessage();
            } else if (cmds[0].equals("qp")) {
                queryPopularity();
            } else if (cmds[0].equals("dce")) {
                deleteColdEmoji();
            } else if (cmds[0].equals("qm")) {
                queryMoney();
            } else if (cmds[0].equals("qlc")) {
                queryLeastConnection();
            } else if (cmds[0].equals("cn")) {
                clearNotices();
            } else {
                assert (false);
            }
        }
        cin.close();
    }

    private void clearNotices() {
        int id = Integer.parseInt(cmds[1]);
        try {
            network.clearNotices(id);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void queryLeastConnection() {
        int id = Integer.parseInt(cmds[1]);
        int ret = 0;
        try {
            ret = network.queryLeastConnection(id);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void queryMoney() {
        int id = Integer.parseInt(cmds[1]);
        int ret = 0;
        try {
            ret = network.queryMoney(id);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void queryBlockSum() {
        System.out.println(network.queryBlockSum());
    }

    private void sendIndirectMessage() {
        int messageId = Integer.parseInt(cmds[1]);
        int ret = 0;
        try {
            ret = network.sendIndirectMessage(messageId);
        } catch (MessageIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void delFromGroup() {
        int id1 = Integer.parseInt(cmds[1]);
        int id2 = Integer.parseInt(cmds[2]);
        try {
            network.delFromGroup(id1, id2);
        } catch (GroupIdNotFoundException e) {
            e.print();
            return;
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (EqualPersonIdException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void queryGroupAgeVar() {
        int id = Integer.parseInt(cmds[1]);
        int ret = 0;
        try {
            ret = network.queryGroupAgeVar(id);
        } catch (GroupIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void queryGroupValueSum() {
        int id = Integer.parseInt(cmds[1]);
        int ret = 0;
        try {
            ret = network.queryGroupValueSum(id);
        } catch (GroupIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void queryGroupPeopleSum() {
        int id = Integer.parseInt(cmds[1]);
        int ret = 0;
        try {
            ret = network.queryGroupPeopleSum(id);
        } catch (GroupIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void addToGroup() {
        int id1 = Integer.parseInt(cmds[1]);
        int id2 = Integer.parseInt(cmds[2]);
        try {
            network.addToGroup(id1, id2);
        } catch (GroupIdNotFoundException e) {
            e.print();
            return;
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (EqualPersonIdException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void addGroup()
            throws InstantiationException, IllegalAccessException,
            IllegalArgumentException, InvocationTargetException {
        int id = Integer.parseInt(cmds[1]);
        try {
            network.addGroup((Group) this.groupConstructor.newInstance(id));
        } catch (EqualGroupIdException e) {
            e.print();
            return;
        }
        System.out.println("Ok");
    }

    private void queryCircle() {
        int id1 = Integer.parseInt(cmds[1]);
        int id2 = Integer.parseInt(cmds[2]);
        boolean ret = false;
        try {
            ret = network.isCircle(id1, id2);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        if (ret == true) {
            System.out.println("1");
        } else {
            System.out.println("0");
        }
    }

    private void queryPeopleSum() {
        int ret = network.queryPeopleSum();
        System.out.println(ret);
    }

    private void queryValue() {
        int id1 = Integer.parseInt(cmds[1]);
        int id2 = Integer.parseInt(cmds[2]);
        int ret = 0;
        try {
            ret = network.queryValue(id1, id2);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (RelationNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void addRelation() {
        int id1 = Integer.parseInt(cmds[1]);
        int id2 = Integer.parseInt(cmds[2]);
        int value = Integer.parseInt(cmds[3]);
        try {
            network.addRelation(id1, id2, value);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        } catch (EqualRelationException e) {
            e.print();
            return;
        }
        System.out.println(String.format("Ok"));
    }

    private void addPerson()
            throws InstantiationException, IllegalAccessException,
            IllegalArgumentException, InvocationTargetException {
        int id = Integer.parseInt(cmds[1]);
        String name = cmds[2];
        int age = Integer.parseInt(cmds[3]);
        try {
            network.addPerson((Person) this.personConstructor.newInstance(
                    id, name, age));
        } catch (EqualPersonIdException e) {
            e.print();
            return;
        }
        System.out.println(String.format("Ok"));
    }

    private void storeEmojiId() {
        int id = Integer.parseInt(cmds[1]);
        try {
            network.storeEmojiId(id);
        } catch (EqualEmojiIdException e) {
            e.print();
            return;
        }
        System.out.println(String.format("Ok"));
    }

    private void addMessage() throws IllegalAccessException, InvocationTargetException, InstantiationException {
        int id = Integer.parseInt(cmds[1]);
        int socialValue = Integer.parseInt(cmds[2]);
        int type = Integer.parseInt(cmds[3]);
        int id1 = Integer.parseInt(cmds[4]);
        int id2 = Integer.parseInt(cmds[5]);
        if (type == 0) {
            if (!network.contains(id1) || !network.contains(id2)) {
                System.out.println(String.format("The person with this number does not exist"));
                return;
            }
            Person person1 = network.getPerson(id1);
            Person person2 = network.getPerson(id2);
            Message message = this.messageConstructor0.newInstance(id, socialValue, person1, person2);
            try {
                network.addMessage(message);
            } catch (EqualMessageIdException e) {
                e.print();
                return;
            } catch (EmojiIdNotFoundException e) {
                e.print();
                return;
            } catch (EqualPersonIdException e) {
                e.print();
                return;
            }
        } else if (type == 1) {
            Group group = network.getGroup(id2);
            if (group == null) {
                System.out.println("Group does not exist");
                return;
            }
            if (!network.contains(id1)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            Message message = this.messageConstructor1.newInstance(id, socialValue, person1, group);
            try {
                network.addMessage(message);
            } catch (EqualMessageIdException e) {
                e.print();
                return;
            } catch (EmojiIdNotFoundException e) {
                e.print();
                return;
            } catch (EqualPersonIdException e) {
                e.print();
                return;
            }
        } else {
            return;
        }
        System.out.println(String.format("Ok"));
    }

    private void addRedEnvelopeMessage() throws IllegalAccessException, InvocationTargetException, InstantiationException {
        int id = Integer.parseInt(cmds[1]);
        int money = Integer.parseInt(cmds[2]);
        int type = Integer.parseInt(cmds[3]);
        int id1 = Integer.parseInt(cmds[4]);
        int id2 = Integer.parseInt(cmds[5]);
        if (type == 0) {
            if (!network.contains(id1) || !network.contains(id2)) {
                System.out.println(String.format("The person with this number does not exist"));
                return;
            }
            Person person1 = network.getPerson(id1);
            Person person2 = network.getPerson(id2);
            RedEnvelopeMessage message = this.redEnvelopeConstructor0.newInstance(id, money, person1, person2);
            try {
                network.addMessage(message);
            } catch (EqualMessageIdException e) {
                e.print();
                return;
            } catch (EmojiIdNotFoundException e) {
                e.print();
                return;
            } catch (EqualPersonIdException e) {
                e.print();
                return;
            }
        } else if (type == 1) {
            Group group = network.getGroup(id2);
            if (group == null) {
                System.out.println("Group does not exist");
                return;
            }
            if (!network.contains(id1)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            RedEnvelopeMessage message = this.redEnvelopeConstructor1.newInstance(id, money, person1, group);
            try {
                network.addMessage(message);
            } catch (EqualMessageIdException e) {
                e.print();
                return;
            } catch (EmojiIdNotFoundException e) {
                e.print();
                return;
            } catch (EqualPersonIdException e) {
                e.print();
                return;
            }
        } else {
            return;
        }
        System.out.println(String.format("Ok"));
    }

    private void addNoticeMessage() throws IllegalAccessException, InvocationTargetException, InstantiationException {
        int id = Integer.parseInt(cmds[1]);
        String string = cmds[2];
        int type = Integer.parseInt(cmds[3]);
        int id1 = Integer.parseInt(cmds[4]);
        int id2 = Integer.parseInt(cmds[5]);
        if (type == 0) {
            if (!network.contains(id1) || !network.contains(id2)) {
                System.out.println(String.format("The person with this number does not exist"));
                return;
            }
            Person person1 = network.getPerson(id1);
            Person person2 = network.getPerson(id2);
            NoticeMessage message = this.noticeConstructor0.newInstance(id, string, person1, person2);
            try {
                network.addMessage(message);
            } catch (EqualMessageIdException e) {
                e.print();
                return;
            } catch (EmojiIdNotFoundException e) {
                e.print();
                return;
            } catch (EqualPersonIdException e) {
                e.print();
                return;
            }
        } else if (type == 1) {
            Group group = network.getGroup(id2);
            if (group == null) {
                System.out.println("Group does not exist");
                return;
            }
            if (!network.contains(id1)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            NoticeMessage message = this.noticeConstructor1.newInstance(id, string, person1, group);
            try {
                network.addMessage(message);
            } catch (EqualMessageIdException e) {
                e.print();
                return;
            } catch (EmojiIdNotFoundException e) {
                e.print();
                return;
            } catch (EqualPersonIdException e) {
                e.print();
                return;
            }
        } else {
            return;
        }
        System.out.println(String.format("Ok"));
    }

    private void addEmojiMessage() throws IllegalAccessException, InvocationTargetException, InstantiationException {
        int id = Integer.parseInt(cmds[1]);
        int emojiId = Integer.parseInt(cmds[2]);
        int type = Integer.parseInt(cmds[3]);
        int id1 = Integer.parseInt(cmds[4]);
        int id2 = Integer.parseInt(cmds[5]);
        if (type == 0) {
            if (!network.contains(id1) || !network.contains(id2)) {
                System.out.println(String.format("The person with this number does not exist"));
                return;
            }
            Person person1 = network.getPerson(id1);
            Person person2 = network.getPerson(id2);
            EmojiMessage message = this.emojiConstructor0.newInstance(id, emojiId, person1, person2);
            try {
                network.addMessage(message);
            } catch (EqualMessageIdException e) {
                e.print();
                return;
            } catch (EmojiIdNotFoundException e) {
                e.print();
                return;
            } catch (EqualPersonIdException e) {
                e.print();
                return;
            }
        } else if (type == 1) {
            Group group = network.getGroup(id2);
            if (group == null) {
                System.out.println("Group does not exist");
                return;
            }
            if (!network.contains(id1)) {
                System.out.println("The person with this number does not exist");
                return;
            }
            Person person1 = network.getPerson(id1);
            EmojiMessage message = this.emojiConstructor1.newInstance(id, emojiId, person1, group);
            try {
                network.addMessage(message);
            } catch (EqualMessageIdException e) {
                e.print();
                return;
            } catch (EmojiIdNotFoundException e) {
                e.print();
                return;
            } catch (EqualPersonIdException e) {
                e.print();
                return;
            }
        } else {
            return;
        }
        System.out.println(String.format("Ok"));
    }

    private void sendMessage() {
        int messageId = Integer.parseInt(cmds[1]);
        try {
            network.sendMessage(messageId);
        } catch (RelationNotFoundException e) {
            e.print();
            return;
        } catch (MessageIdNotFoundException e) {
            e.print();
            return;
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(String.format("Ok"));
    }

    private void querySocialValue() {
        int id = Integer.parseInt(cmds[1]);
        int ret = 0;
        try {
            ret = network.querySocialValue(id);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void queryPopularity() {
        int id = Integer.parseInt(cmds[1]);
        int ret = 0;
        try {
            ret = network.queryPopularity(id);
        } catch (EmojiIdNotFoundException e) {
            e.print();
            return;
        }
        System.out.println(ret);
    }

    private void deleteColdEmoji() {
        int limit = Integer.parseInt(cmds[1]);
        int ret = 0;
        ret = network.deleteColdEmoji(limit);
        System.out.println(ret);
    }

    private void queryReceivedMessages() {
        int id = Integer.parseInt(cmds[1]);
        List<Message> list = new ArrayList<>();
        try {
            list = network.queryReceivedMessages(id);
        } catch (PersonIdNotFoundException e) {
            e.print();
            return;
        }
        if (list.size() == 0) {
            System.out.println("None");
        } else {
            int i = 0;
            for (; i < list.size() - 1; i++) {
                Message message = list.get(i);
                resolve(message);
                System.out.print("; ");
            }
            Message message = list.get(i);
            resolve(message);
            System.out.println();
        }
    }

    private void resolve(Message message) {
        if (message instanceof NoticeMessage) {
            System.out.print("notice: " + ((NoticeMessage) message).getString());
        } else if (message instanceof EmojiMessage) {
            System.out.print("Emoji: " + ((EmojiMessage) message).getEmojiId());
        } else if (message instanceof RedEnvelopeMessage) {
            System.out.print("RedEnvelope: " + ((RedEnvelopeMessage) message).getMoney());
        } else {
            System.out.print("Ordinary message");
        }
    }
}
