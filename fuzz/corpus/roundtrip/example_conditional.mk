CC ?= gcc
CFLAGS = -Wall -O2

ifeq ($(DEBUG),1)
CFLAGS += -g
else
CFLAGS += -DNDEBUG
endif

ifdef VERBOSE
Q =
else
Q = @
endif

include config.mk
-include optional.mk

.PHONY: all clean
all: hello

hello: hello.o util.o
	$(Q)$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(Q)$(CC) $(CFLAGS) -c -o $@ $<

clean:
	rm -f hello *.o
