libfoo.a(bar.o baz.o): bar.c baz.c
	$(CC) -c bar.c -o bar.o
	$(CC) -c baz.c -o baz.o
	ar rcs $@ bar.o baz.o
