package com.oocourse.spec2.main;

import java.util.List;

import com.oocourse.spec2.exceptions.EqualGroupIdException;
import com.oocourse.spec2.exceptions.EqualMessageIdException;
import com.oocourse.spec2.exceptions.EqualPersonIdException;
import com.oocourse.spec2.exceptions.EqualRelationException;
import com.oocourse.spec2.exceptions.GroupIdNotFoundException;
import com.oocourse.spec2.exceptions.MessageIdNotFoundException;
import com.oocourse.spec2.exceptions.PersonIdNotFoundException;
import com.oocourse.spec2.exceptions.RelationNotFoundException;

public interface Network {

    /*@ public instance model non_null Person[] people;
      @ public instance model non_null Group[] groups;
      @ public instance model non_null Message[] messages;
      @*/

    //@ ensures \result == (\exists int i; 0 <= i && i < people.length; people[i].getId() == id);
    public /*@ pure @*/ boolean contains(int id);

    /*@ public normal_behavior
      @ requires contains(id);
      @ ensures (\exists int i; 0 <= i && i < people.length; people[i].getId() == id &&
      @         \result == people[i]);
      @ also
      @ public normal_behavior
      @ requires !contains(id);
      @ ensures \result == null;
      @*/
    public /*@ pure @*/ Person getPerson(int id);

    /*@ public normal_behavior
      @ requires !(\exists int i; 0 <= i && i < people.length; people[i].equals(person));
      @ assignable people;
      @ ensures people.length == \old(people.length) + 1;
      @ ensures (\forall int i; 0 <= i && i < \old(people.length);
      @          (\exists int j; 0 <= j && j < people.length; people[j] == (\old(people[i]))));
      @ ensures (\exists int i; 0 <= i && i < people.length; people[i] == person);
      @ also
      @ public exceptional_behavior
      @ signals (EqualPersonIdException e) (\exists int i; 0 <= i && i < people.length;
      @                                     people[i].equals(person));
      @*/
    public void addPerson(/*@ non_null @*/Person person) throws EqualPersonIdException;

    /*@ public normal_behavior
      @ requires contains(id1) && contains(id2) && !getPerson(id1).isLinked(getPerson(id2));
      @ assignable people;
      @ ensures people.length == \old(people.length);
      @ ensures (\forall int i; 0 <= i && i < \old(people.length);
      @          (\exists int j; 0 <= j && j < people.length; people[j] == \old(people[i])));
      @ ensures (\forall int i; 0 <= i && i < people.length && \old(people[i].getId()) != id1 &&
      @     \old(people[i].getId()) != id2; \not_assigned(people[i]));
      @ ensures getPerson(id1).isLinked(getPerson(id2)) && getPerson(id2).isLinked(getPerson(id1));
      @ ensures getPerson(id1).queryValue(getPerson(id2)) == value;
      @ ensures getPerson(id2).queryValue(getPerson(id1)) == value;
      @ ensures (\forall int i; 0 <= i && i < \old(getPerson(id1).acquaintance.length);
      @         \old(getPerson(id1).acquaintance[i]) == getPerson(id1).acquaintance[i] &&
      @          \old(getPerson(id1).value[i]) == getPerson(id1).value[i]);
      @ ensures (\forall int i; 0 <= i && i < \old(getPerson(id2).acquaintance.length);
      @         \old(getPerson(id2).acquaintance[i]) == getPerson(id2).acquaintance[i] &&
      @          \old(getPerson(id2).value[i]) == getPerson(id2).value[i]);
      @ ensures getPerson(id1).value.length == getPerson(id1).acquaintance.length;
      @ ensures getPerson(id2).value.length == getPerson(id2).acquaintance.length;
      @ ensures \old(getPerson(id1).value.length) == getPerson(id1).acquaintance.length - 1;
      @ ensures \old(getPerson(id2).value.length) == getPerson(id2).acquaintance.length - 1;
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ requires !contains(id1) || !contains(id2) || getPerson(id1).isLinked(getPerson(id2));
      @ signals (PersonIdNotFoundException e) !contains(id1);
      @ signals (PersonIdNotFoundException e) contains(id1) && !contains(id2);
      @ signals (EqualRelationException e) contains(id1) && contains(id2) &&
      @         getPerson(id1).isLinked(getPerson(id2));
      @*/
    public void addRelation(int id1, int id2, int value) throws
            PersonIdNotFoundException, EqualRelationException;

    /*@ public normal_behavior
      @ requires contains(id1) && contains(id2) && getPerson(id1).isLinked(getPerson(id2));
      @ ensures \result == getPerson(id1).queryValue(getPerson(id2));
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !contains(id1);
      @ signals (PersonIdNotFoundException e) contains(id1) && !contains(id2);
      @ signals (RelationNotFoundException e) contains(id1) && contains(id2) &&
      @         !getPerson(id1).isLinked(getPerson(id2));
      @*/
    public /*@ pure @*/ int queryValue(int id1, int id2) throws
            PersonIdNotFoundException, RelationNotFoundException;

    //@ ensures \result == people.length;
    public /*@ pure @*/ int queryPeopleSum();

    /*@ public normal_behavior
      @ requires contains(id1) && contains(id2);
      @ ensures \result == (\exists Person[] array; array.length >= 2;
      @                     array[0].equals(getPerson(id1)) &&
      @                     array[array.length - 1].equals(getPerson(id2)) &&
      @                      (\forall int i; 0 <= i && i < array.length - 1;
      @                      array[i].isLinked(array[i + 1]) == true));
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !contains(id1);
      @ signals (PersonIdNotFoundException e) contains(id1) && !contains(id2);
      @*/
    public /*@ pure @*/ boolean isCircle(int id1, int id2) throws PersonIdNotFoundException;

    /*@ ensures \result ==
      @         (\sum int i; 0 <= i && i < people.length &&
      @         (\forall int j; 0 <= j && j < i; !isCircle(people[i].getId(), people[j].getId()));
      @         1);
      @*/
    public /*@ pure @*/ int queryBlockSum();

    /*@ public normal_behavior
      @ requires contains(id);
      @ ensures \result ==
      @         (\min Person[] subgroup; subgroup.length % 2 == 0 &&
      @           (\forall int i; 0 <= i && i < subgroup.length / 2; subgroup[i * 2].isLinked(subgroup[i * 2 + 1])) &&
      @           (\forall int i; 0 <= i && i < people.length; isCircle(id, people[i].getId()) <==>
      @             (\exists int j; 0 <= j && j < subgroup.length; subgroup[j].equals(people[i]))) &&
      @           (\forall int i; 0 <= i && i < people.length; isCircle(id, people[i].getId()) <==>
      @             (\exists Person[] connection;
      @               (\forall int j; 0 <= j && j < connection.length - 1;
      @                 (\exists int k; 0 <= k && k < subgroup.length / 2; subgroup[k * 2].equals(connection[j]) &&
      @                   subgroup[k * 2 + 1].equals(connection[j + 1])));
      @                connection[0].equals(getPerson(id)) && connection[connection.length - 1].equals(people[i])));
      @           (\sum int i; 0 <= i && i < subgroup.length / 2; subgroup[i * 2].queryValue(subgroup[i * 2 + 1])));
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !contains(id);
      @*/
    public /*@ pure @*/ int queryLeastConnection(int id) throws PersonIdNotFoundException;

    /*@ public normal_behavior
      @ requires !(\exists int i; 0 <= i && i < groups.length; groups[i].equals(group));
      @ assignable groups;
      @ ensures groups.length == \old(groups.length) + 1;
      @ ensures (\forall int i; 0 <= i && i < \old(groups.length);
      @          (\exists int j; 0 <= j && j < groups.length; groups[j] == (\old(groups[i]))));
      @ ensures (\exists int i; 0 <= i && i < groups.length; groups[i] == group);
      @ also
      @ public exceptional_behavior
      @ signals (EqualGroupIdException e) (\exists int i; 0 <= i && i < groups.length;
      @                                     groups[i].equals(group));
      @*/
    public void addGroup(/*@ non_null @*/Group group) throws EqualGroupIdException;

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id);
      @ ensures (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id &&
      @         \result == groups[i]);
      @ also
      @ public normal_behavior
      @ requires (\forall int i; 0 <= i && i < groups.length; groups[i].getId() != id);
      @ ensures \result == null;
      @*/
    public /*@ pure @*/ Group getGroup(int id);

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id2) &&
      @           (\exists int i; 0 <= i && i < people.length; people[i].getId() == id1) &&
      @            getGroup(id2).hasPerson(getPerson(id1)) == false &&
      @             getGroup(id2).people.length < 1111;
      @ assignable getGroup(id2).people;
      @ ensures (\forall Person i; \old(getGroup(id2).hasPerson(i));
      @          getGroup(id2).hasPerson(i));
      @ ensures \old(getGroup(id2).people.length) == getGroup(id2).people.length - 1;
      @ ensures getGroup(id2).hasPerson(getPerson(id1));
      @ also
      @ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id2) &&
      @           (\exists int i; 0 <= i && i < people.length; people[i].getId() == id1) &&
      @            getGroup(id2).hasPerson(getPerson(id1)) == false && 
      @             getGroup(id2).people.length >= 1111;
      @ assignable \nothing;
      @ also
      @ public exceptional_behavior
      @ signals (GroupIdNotFoundException e) !(\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2);
      @ signals (PersonIdNotFoundException e) (\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2) && !(\exists int i; 0 <= i && i < people.length;
      @           people[i].getId() == id1);
      @ signals (EqualPersonIdException e) (\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2) && (\exists int i; 0 <= i && i < people.length;
      @           people[i].getId() == id1) && getGroup(id2).hasPerson(getPerson(id1));
      @*/
    public void addToGroup(int id1, int id2) throws GroupIdNotFoundException,
            PersonIdNotFoundException, EqualPersonIdException;

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id);
      @ ensures \result == getGroup(id).people.length;
      @ also
      @ public exceptional_behavior
      @ signals (GroupIdNotFoundException e) !(\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id);
      @*/
    public /*@ pure @*/ int queryGroupPeopleSum(int id) throws GroupIdNotFoundException;

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id);
      @ ensures \result == getGroup(id).getValueSum();
      @ also
      @ public exceptional_behavior
      @ signals (GroupIdNotFoundException e) !(\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id);
      @*/
    public /*@ pure @*/ int queryGroupValueSum(int id) throws GroupIdNotFoundException;

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id);
      @ ensures \result == getGroup(id).getAgeVar();
      @ also
      @ public exceptional_behavior
      @ signals (GroupIdNotFoundException e) !(\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id);
      @*/
    public /*@ pure @*/ int queryGroupAgeVar(int id) throws GroupIdNotFoundException;

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id2) &&
      @           (\exists int i; 0 <= i && i < people.length; people[i].getId() == id1) &&
      @            getGroup(id2).hasPerson(getPerson(id1)) == true;
      @ assignable getGroup(id2).people;
      @ ensures (\forall Person i; getGroup(id2).hasPerson(i);
      @          \old(getGroup(id2).hasPerson(i)));
      @ ensures \old(getGroup(id2).people.length) == getGroup(id2).people.length + 1;
      @ ensures getGroup(id2).hasPerson(getPerson(id1)) == false;
      @ also
      @ public exceptional_behavior
      @ signals (GroupIdNotFoundException e) !(\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2);
      @ signals (PersonIdNotFoundException e) (\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2) && !(\exists int i; 0 <= i && i < people.length;
      @           people[i].getId() == id1);
      @ signals (EqualPersonIdException e) (\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2) && (\exists int i; 0 <= i && i < people.length;
      @           people[i].getId() == id1) && !getGroup(id2).hasPerson(getPerson(id1));
      @*/
    public void delFromGroup(int id1, int id2)
            throws GroupIdNotFoundException, PersonIdNotFoundException, EqualPersonIdException;

    //@ ensures \result == (\exists int i; 0 <= i && i < messages.length; messages[i].getId() == id);
    public /*@ pure @*/ boolean containsMessage(int id);

    /*@ public normal_behavior
      @ requires !(\exists int i; 0 <= i && i < messages.length; messages[i].equals(message)) &&
      @           ((message.getType() == 0) ==> (message.getPerson1() != message.getPerson2()));
      @ assignable messages;
      @ ensures messages.length == \old(messages.length) + 1;
      @ ensures (\forall int i; 0 <= i && i < \old(messages.length);
      @          (\exists int j; 0 <= j && j < messages.length; messages[j].equals(\old(messages[i]))));
      @ ensures (\exists int i; 0 <= i && i < messages.length; messages[i].equals(message));
      @ also
      @ public exceptional_behavior
      @ signals (EqualMessageIdException e) (\exists int i; 0 <= i && i < messages.length;
      @                                     messages[i].equals(message));
      @ signals (EqualPersonIdException e) !(\exists int i; 0 <= i && i < messages.length;
      @                                     messages[i].equals(message)) &&
      @                                     message.getType() == 0 && message.getPerson1() == message.getPerson2();
      @*/
    public void addMessage(Message message) throws
            EqualMessageIdException, EqualPersonIdException;

    /*@ public normal_behavior
      @ requires containsMessage(id);
      @ ensures (\exists int i; 0 <= i && i < messages.length; messages[i].getId() == id &&
      @         \result == messages[i]);
      @ public normal_behavior
      @ requires !containsMessage(id);
      @ ensures \result == null;
      @*/
    public /*@ pure @*/ Message getMessage(int id);


    /*@ public normal_behavior
      @ requires containsMessage(id) && getMessage(id).getType() == 0 &&
      @          getMessage(id).getPerson1().isLinked(getMessage(id).getPerson2()) &&
      @          getMessage(id).getPerson1() != getMessage(id).getPerson2();
      @ assignable messages;
      @ assignable getMessage(id).getPerson1().socialValue;
      @ assignable getMessage(id).getPerson2().messages, getMessage(id).getPerson2().socialValue;
      @ ensures \old(getMessage(id)).getPerson1().getSocialValue() ==
      @         \old(getMessage(id).getPerson1().getSocialValue()) + \old(getMessage(id)).getSocialValue() &&
      @         \old(getMessage(id)).getPerson2().getSocialValue() ==
      @         \old(getMessage(id).getPerson2().getSocialValue()) + \old(getMessage(id)).getSocialValue();
      @ ensures !containsMessage(id) && messages.length == \old(messages.length) - 1 &&
      @         (\forall int i; 0 <= i && i < \old(messages.length) && \old(messages[i].getId()) != id;
      @         (\exists int j; 0 <= j && j < messages.length; messages[j].equals(\old(messages[i]))));
      @ ensures (\forall int i; 0 <= i && i < \old(getMessage(id).getPerson2().getMessages().size());
      @          \old(getMessage(id)).getPerson2().getMessages().get(i+1) == \old(getMessage(id).getPerson2().getMessages().get(i)));
      @ ensures \old(getMessage(id)).getPerson2().getMessages().get(0) == \old(getMessage(id));
      @ ensures \old(getMessage(id)).getPerson2().getMessages().size() == \old(getMessage(id).getPerson2().getMessages().size()) + 1;
      @ also
      @ public normal_behavior
      @ requires containsMessage(id) && getMessage(id).getType() == 1 &&
      @           getMessage(id).getGroup().hasPerson(getMessage(id).getPerson1());
      @ assignable people[*].socialValue, messages;
      @ ensures (\forall Person p; getMessage(id).getGroup().hasPerson(p); p.getSocialValue() ==
      @         \old(p.getSocialValue()) + getMessage(id).getSocialValue());
      @ ensures (\forall int i; 0 <= i && i < people.length && !getMessage(id).getGroup().hasPerson(people[i]);
      @          \old(people[i].getSocialValue()) == people[i].getSocialValue());
      @ ensures !containsMessage(id) && messages.length == \old(messages.length) - 1 &&
      @         (\forall int i; 0 <= i && i < \old(messages.length) && \old(messages[i].getId()) != id;
      @         (\exists int j; 0 <= j && j < messages.length; messages[j].equals(\old(messages[i]))));
      @ also
      @ public exceptional_behavior
      @ signals (MessageIdNotFoundException e) !containsMessage(id);
      @ signals (RelationNotFoundException e) containsMessage(id) && getMessage(id).getType() == 0 &&
      @          !(getMessage(id).getPerson1().isLinked(getMessage(id).getPerson2()));
      @ signals (PersonIdNotFoundException e) containsMessage(id) && getMessage(id).getType() == 1 &&
      @          !(getMessage(id).getGroup().hasPerson(getMessage(id).getPerson1()));
      @*/
    public void sendMessage(int id) throws
            RelationNotFoundException, MessageIdNotFoundException, PersonIdNotFoundException;

    /*@ public normal_behavior
      @ requires contains(id);
      @ ensures \result == getPerson(id).getSocialValue();
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !contains(id);
      @*/
    public /*@ pure @*/ int querySocialValue(int id) throws PersonIdNotFoundException;

    /*@ public normal_behavior
      @ requires contains(id);
      @ ensures \result == getPerson(id).getReceivedMessages();
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !contains(id);
      @*/
    public /*@ pure @*/ List<Message> queryReceivedMessages(int id) throws PersonIdNotFoundException;
}
