package com.oocourse.spec3.main;

public class MyRedEnvelopeMessage implements RedEnvelopeMessage {

    private int id;
    private int type;
    private Person person1;
    private Person person2;
    private Group group;
    private int money;

    /*@ ensures type == 0;
      @ ensures group == null;
      @ ensures id == messageId;
      @ ensures person1 == messagePerson1;
      @ ensures person2 == messagePerson2;
      @ ensures money == luckyMoney;
      @*/
    public MyRedEnvelopeMessage(int messageId, int luckyMoney,
                                Person messagePerson1, Person messagePerson2) {
        this.type = 0;
        this.group = null;
        this.id = messageId;
        this.person1 = messagePerson1;
        this.person2 = messagePerson2;
        this.money = luckyMoney;
    }

    /*@ ensures type == 1;
      @ ensures person2 == null;
      @ ensures id == messageId;
      @ ensures person1 == messagePerson1;
      @ ensures group == messageGroup;
      @ ensures money == luckyMoney;
      @*/
    public MyRedEnvelopeMessage(int messageId, int luckyMoney,
                                Person messagePerson1, Group messageGroup) {
        this.type = 1;
        this.group = messageGroup;
        this.id = messageId;
        this.person1 = messagePerson1;
        this.person2 = null;
        this.money = luckyMoney;
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
        return money * 5;
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
    public int getMoney() {
        return money;
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