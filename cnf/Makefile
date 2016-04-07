CC = g++

CFLAGS = -std=c++11

OBJS = cnf.o

cnf: $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) -o cnf

cnf.o: cnf.cc FormulaTree.h
	$(CC) $(CFLAGS) -c cnf.cc

clean:
	-rm cnf
	-rm $(OBJS)
