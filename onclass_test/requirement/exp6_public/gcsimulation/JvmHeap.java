package gcsimulation;

import java.util.Arrays;
import java.util.List;

public class JvmHeap extends MyHeap<MyObject> {

    JvmHeap(int capacity) {
        super(capacity);
    }

    /*@ public normal_behavior
      @ requires objectId != null;
      @ assignable elements[*].referenced;
      @ ensures size == \old(size);
      @ [1]; 要求：定义后置条件，表示调用此方法前后，elements数组中下标大于等于1且小于等于size，
      @  并且其id不在objectId中的元素保持不变。不可使用原子表达式\not_assigned与\not_modified。
      @ ensures (\forall int i; 1 <= i && i <= size;
      @          (\exists int j; 0 <= j && j < objectId.size();
      @            objectId.get(j) == elements[i].getId()) ==>  (!elements[i].isReferenced()));
      @*/
    public void setUnreferencedId(List<Integer> objectId) {
        for (int id : objectId) {
            for (int i = 1; i <= this.getSize(); i++) {
                MyObject myObject =  this.getElement(i);
                if (myObject.getId() == id) {
                    myObject.setUnreferenced();
                    setElementData(i, myObject);
                }
            }
        }
    }

    /*@ public normal_behavior
      @ assignable elements, size;
      @ ensures size == (\sum int i; 1 <= i && i <= \old(size) &&
      @                              \old(elements[i].isReferenced()); 1);
      @ ensures (\forall int i; 1 <= i && i <= \old(size);
      @          \old(elements[i].isReferenced()) ==>
      @           (\exists int j; 1 <= j && j <= size; elements[j].equals(\old(getElement(i)))));
      @ ensures (\forall int i; 1 <= i && i <= \old(size);
      @          !(\old(elements[i].isReferenced())) ==>
      @           (\forall int j; 1 <= j && j <= size;
      @           !elements[j].equals(\old(elements[i]))));
      @ ensures (\forall int i; 1 <= i && i <= size;
      @          (\exists int j; 1 <= j && j <= \old(size);
      @          elements[i].equals(\old(elements[j]))));
      @*/
    public void removeUnreferenced() {
        // TODO
    }

    /*@ public normal_behavior
      @ requires size > 0;
      @ ensures (\forall int i; 1 <= i && i <= size; \result.compareTo(elements[i]) <= 0);
      @ ensures (\exists int i; 1 <= i && i <= size; \result == elements[i]);
      @ also
      @ public normal_behavior
      @ requires size == 0;
      @ ensures \result == null;
      @*/
    public /*@ pure @*/ MyObject getYoungestOne() {
        // TODO
    }

    // 注：helper表示该函数的作用不受invariant约束（即该函数执行前后不是不变式的可见状态）
    private /*@ helper @*/ void rebuild() {
        Arrays.sort(getElementData(), 1, getSize() + 1);
    }
}