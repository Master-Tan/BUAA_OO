package com.oocourse.uml2.interact.format;

import com.oocourse.uml2.interact.exceptions.user.ClassNotFoundException;
import com.oocourse.uml2.interact.exceptions.user.ClassDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.MethodDuplicatedException;
import com.oocourse.uml2.interact.exceptions.user.MethodWrongTypeException;
import com.oocourse.uml2.models.common.Visibility;

import java.util.List;
import java.util.Map;

/**
 * UML交互接口
 */
public interface UmlClassModelApi {
    /**
     * 获取类数量
     * 指令：CLASS_COUNT
     *
     * @return 类数量
     */
    int getClassCount();

    /**
     * 获取类的子类数量
     * 指令：CLASS_SUBCLASS_COUNT
     *
     * @param className 类名
     * @return 直接继承该类的子类数量
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    int getClassSubClassCount(String className)
            throws ClassNotFoundException, ClassDuplicatedException;


    /**
     * 获取类操作数量
     * 指令：CLASS_OPERATION_COUNT
     *
     * @param className 类名
     * @return 类的操作数量
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    int getClassOperationCount(String className)
            throws ClassNotFoundException, ClassDuplicatedException;

    /**
     * 统计类操作可见性
     * 指令：CLASS_OPERATION_VISIBILITY
     *
     * @param className     类名
     * @param methodName 操作名
     * @return 类操作可见性统计结果
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    Map<Visibility, Integer> getClassOperationVisibility(String className, String methodName)
            throws ClassNotFoundException, ClassDuplicatedException;

    /**
     * 查询类的操作的耦合度
     * 指令：CLASS_OPERATION_COUPLING_DEGREE
     *
     * @param className     类名
     * @param methodName 操作名
     * @return 类的操作的耦合度
     * @throws ClassNotFoundException    类未找到异常
     * @throws ClassDuplicatedException  类重复异常
     * @throws MethodWrongTypeException  存在错误类型
     * @throws MethodDuplicatedException 存在重复操作
     */
    List<Integer> getClassOperationCouplingDegree(String className, String methodName)
            throws ClassNotFoundException, ClassDuplicatedException,
            MethodWrongTypeException, MethodDuplicatedException;

    /**
     * 查询类的属性的耦合度
     * 指令：CLASS_ATTR_COUPLING_DEGREE
     *
     * @param className 类名
     * @return 类的属性的耦合度
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    int getClassAttributeCouplingDegree(String className)
            throws ClassNotFoundException, ClassDuplicatedException;


    /**
     * 获取实现的接口列表
     * 指令：CLASS_IMPLEMENT_INTERFACE_LIST
     *
     * @param className 类名
     * @return 实现的接口列表
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    List<String> getClassImplementInterfaceList(String className)
            throws ClassNotFoundException, ClassDuplicatedException;

    /**
     * 获取类的继承深度
     * 指令：CLASS_DEPTH_OF_INHERITANCE
     *
     * @param className 类名
     * @return 类的继承深度
     * @throws ClassNotFoundException   类未找到异常
     * @throws ClassDuplicatedException 类重复异常
     */
    int getClassDepthOfInheritance(String className)
            throws ClassNotFoundException, ClassDuplicatedException;


}
