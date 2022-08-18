package com.oocourse.uml2;

import com.beust.jcommander.JCommander;
import com.oocourse.uml2.args.commands.AbstractCommand;
import com.oocourse.uml2.args.commands.DumpCommand;
import com.oocourse.uml2.args.commands.ListCommand;
import com.oocourse.uml2.args.commands.MainCommand;
import com.oocourse.uml2.args.exceptions.CommandLineProcessException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public abstract class PackageEntrance {
    public static void main(String[] args) throws Exception {
        final List<AbstractCommand> commandList = new ArrayList<AbstractCommand>() {{
            add(new MainCommand());
            add(new DumpCommand());
            add(new ListCommand());
        }};
        Map<String, AbstractCommand> commandMap = new HashMap<String, AbstractCommand>() {{
            for (AbstractCommand command : commandList) {
                put(command.getCommandName(), command);
            }
        }};

        JCommander.Builder builder = JCommander.newBuilder();
        for (Map.Entry<String, AbstractCommand> entry : commandMap.entrySet()) {
            if (entry.getKey() == null) {
                builder.addObject(entry.getValue());
            } else {
                builder.addCommand(entry.getKey(), entry.getValue());
            }
        }

        JCommander jCommander = builder.build();
        jCommander.parse(args);
        AbstractCommand command = commandMap.get(jCommander.getParsedCommand());

        try {
            command.run();
        } catch (CommandLineProcessException e) {
            System.err.println(e.getMessage());
            System.exit(e.getExitCode());
        } catch (Exception e) {
            System.err.println("Something wrong with package, please contact the assistants by hansbug@questionor.cn.");
            throw e;
        }
    }
}
