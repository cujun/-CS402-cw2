CC = g++

CFLAGS = -std=c++11

OBJS = nonogram.o

nonogram: $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) -o nonogram

nonogram.o: nonogram.cc FormulaTree.h
	$(CC) $(CFLAGS) -c nonogram.cc

clean:
	-rm nonogram
	-rm $(OBJS)
