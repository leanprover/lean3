
INCLUDES=/usr/local/lib/libffi-3.2.1/include
LIB=/usr/local/lib/libffi-3.2.1/lib

all: some_file.so client
	./client

%.o: %.c
	gcc -c -fPIC $< -o $@ -I$(INCLUDES)

some_file.so: some_file.o
	gcc some_file.o -shared -o some_file.so

client: client.c
	gcc client.c -o client  -I$(INCLUDES) -lffi -ldl
