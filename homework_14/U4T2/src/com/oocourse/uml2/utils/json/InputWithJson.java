package com.oocourse.uml2.utils.json;

import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

/**
 * 基于JSON读入
 *
 * @param <T> 目标类型
 * @param <E> 异常类型
 */
public interface InputWithJson<T, E extends JsonLoadException> {
    /**
     * 从文件读取数据
     *
     * @param file 文件对象
     * @return 目标数据
     * @throws IOException    读写异常
     * @throws ParseException 解析异常
     */
    default T loadFromFile(File file)
            throws IOException, ParseException, E {
        JSONParser parser = new JSONParser();
        FileReader reader = new FileReader(file);
        Object jsonObject = parser.parse(reader);
        reader.close();
        return loadFromJson(jsonObject);
    }

    /**
     * 从文件读取数据
     *
     * @param filename 文件路径
     * @return 目标数据
     * @throws IOException    读写异常
     * @throws ParseException 解析异常
     */
    default T loadFromFile(String filename)
            throws IOException, ParseException, E {
        return loadFromFile(new File(filename));
    }

    /**
     * 从输入流读取
     *
     * @param inputStream 输入流
     * @param charsetName 字符集名称
     * @return 目标数据
     * @throws IOException    读写异常
     * @throws ParseException 解析异常
     */
    default T loadFromStream(InputStream inputStream, String charsetName)
            throws IOException, ParseException, E {
        JSONParser parser = new JSONParser();
        InputStreamReader reader = new InputStreamReader(inputStream, charsetName);
        Object jsonObject = parser.parse(reader);
        reader.close();
        return loadFromJson(jsonObject);
    }

    /**
     * 从输入流读取
     *
     * @param inputStream 输入流
     * @return 目标数据
     * @throws IOException    读写异常
     * @throws ParseException 解析异常
     */
    default T loadFromStream(InputStream inputStream)
            throws IOException, ParseException, E {
        return loadFromStream(inputStream, null);
    }

    /**
     * 从字符串数据
     *
     * @param jsonString JSON字符串
     * @return 目标数据
     * @throws ParseException 解析异常
     */
    default T loadFromString(String jsonString) throws ParseException, E {
        JSONParser parser = new JSONParser();
        return loadFromJson(parser.parse(jsonString));
    }

    /**
     * 从json数据加载目标数据
     *
     * @param jsonObject json数据
     * @return 目标数据
     */
    T loadFromJson(Object jsonObject) throws E;
}
