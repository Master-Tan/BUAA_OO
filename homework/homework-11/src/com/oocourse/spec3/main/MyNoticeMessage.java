package com.oocourse.spec3.main;

public class MyNoticeMessage implements NoticeMessage {

    private int type;
    private Group group;
    private int id;
    private Person person1;
    private Person person2;
    private String string;

    /*@ ensures type == 0;
      @ ensures group == null;
      @ ensures id == messageId;
      @ ensures person1 == messagePerson1;
      @ ensures person2 == messagePerson2;
      @ ensures string == noticeString;
      @*/
    public MyNoticeMessage(int messageId, String noticeString,
                           Person messagePerson1, Person messagePerson2) {
        this.type = 0;
        this.group = null;
        this.id = messageId;
        this.person1 = messagePerson1;
        this.person2 = messagePerson2;
        this.string = noticeString;
    }

    /*@ ensures type == 1;
      @ ensures person2 == null;
      @ ensures id == messageId;
      @ ensures person1 == messagePerson1;
      @ ensures group == messageGroup;
      @ ensures string == noticeString;
      @*/
    public MyNoticeMessage(int messageId, String noticeString,
                           Person messagePerson1, Group messageGroup) {
        this.type = 1;
        this.group = messageGroup;
        this.id = messageId;
        this.person1 = messagePerson1;
        this.person2 = null;
        // TODO 字符串复制可能有错
        this.string = noticeString;
    }

    @Override
    public int getType() {
        return type;
    }

    @Override
    public int getId() {
        return id;
    }

    @Override
    public int getSocialValue() {
        return string.length();
    }

    @Override
    public Person getPerson1() {
        return person1;
    }

    @Override
    public Person getPerson2() {
        return person2;
    }

    @Override
    public Group getGroup() {
        return group;
    }

    @Override
    public String getString() {
        return string;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof Message) {
            return (((Message) obj).getId() == id);
        } else {
            return false;
        }
    }
}