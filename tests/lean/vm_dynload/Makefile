
all: some_file.so client
	./client

%.o: %.c
	gcc -c -fPIC $< -o $@

some_file.so: some_file.o
	gcc some_file.o -shared -o some_file.so

client: client.c
	gcc client.c -o client
