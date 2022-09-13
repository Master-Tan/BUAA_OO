package com.oocourse.uml2.models.common;

import com.oocourse.uml2.models.elements.UmlElement;

import java.util.Collections;
import java.util.HashMap;
import java.util.Objects;

/**
 * 依赖类
 */
public class ReferenceType implements NameableType {
    private final String referenceId;

    /**
     * 构造函数
     *
     * @param referenceId 依赖标签
     */
    ReferenceType(String referenceId) {
        this.referenceId = referenceId;
    }

    /**
     * 获取依赖标签
     *
     * @return 依赖标签
     */
    public String getReferenceId() {
        return referenceId;
    }

    /**
     * 相等性判断
     *
     * @param o 对象
     * @return 是否相等
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ReferenceType that = (ReferenceType) o;
        return Objects.equals(referenceId, that.referenceId);
    }

    /**
     * 哈希值求解
     *
     * @return 哈希值
     */
    @Override
    public int hashCode() {
        return Objects.hash(referenceId);
    }

    /**
     * 转为json数据
     *
     * @return json数据
     */
    @Override
    public Object toJson() {
        return Collections.unmodifiableMap(new HashMap<String, Object>() {{
            put(UmlElement.REF_KEY, referenceId);
        }});
    }
}
