## task1

- extends Thread

- Thread thread = new Thread(process2); thread.start();

  

## task2

- 为代码添加输出即可查看 

  

## task3

- C

  

## task4

```java 
public class Consumer extends Thread {
    private Tray tray;

    public Consumer(Tray t) {
        tray = t;
    }

    public void run() {
        for (int i = 1; i <= 10; i++) {
            tray.get();
        }
    }
}

public class Producer extends Thread {
    private Tray tray;

    public Producer(Tray t) {
        tray = t;
    }

    public void run() {
        for (int i = 1; i <= 10; i++) {
            tray.put(i);
            try {
                sleep((int) (Math.random() * 100));
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
    }
}

public class Tray {
    private int value;
    private boolean full;

    Tray() {
        full = false;
    }

    public synchronized void get() {
        while (!full) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        System.out.println("Consumer get:" + value);
        full = false;
        notifyAll();
    }

    public synchronized void put(int v) {
        while (full) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        System.out.println("Producer put:" + v);
        full = true;
        value = v;
        notifyAll();
    }
}

public class ProducerConsumerTest {
    public static void main(String[] args) {
        Tray t = new Tray();
        Producer p1 = new Producer(t);
        Consumer c1 = new Consumer(t);
        p1.start();
        c1.start();
    }
}
```



## task5

```java
import java.util.ArrayList;
import java.util.List;

public class Server implements Observerable {
    private List<Observer> list;

    public Server() {
        list = new ArrayList<Observer>();
    }

    @Override
    public void addObserver(Observer o) {
        list.add(o);
    }

    @Override
    public void removeObserver(Observer o) {
        list.remove(o);
    }

    @Override
    public void notifyObserver(String message) {
        System.out.println("server: " + message);
        for(int i = 0; i < list.size(); i++) {
            Observer oserver = list.get(i);
            oserver.update(message);
        }
    }
}

```

```java
public class User implements Observer {
    private String name;

    public User(String name) {
        this.name = name;
    }

    @Override
    public void update(String message) {
        System.out.println(name + ": " + message);
    }
}

```

