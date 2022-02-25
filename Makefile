CC=cc
CFLAGS=-O2 -pipe -Wall -Wextra -Wpedantic -Wshadow
CC_COMMAND=$(CC) $(CFLAGS) -std=c90

all: pdld

pdld: main.o
	$(CC_COMMAND) main.o -o pdld

main.o: main.c
	$(CC_COMMAND) -c main.c -o main.o

clean:
	rm -f pdld main.o
