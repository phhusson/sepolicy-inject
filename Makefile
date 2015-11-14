CFLAGS ?= -g -Wall -Werror -Wshadow -O2 -pipe -std=gnu11
LIBDIR ?= libsepol/src
LDLIBS=$(LIBDIR)/libsepol.a

all:libsepol.a sepolicy-inject

libsepol.a:
	$(MAKE) -C libsepol/src

sepolicy-inject:sepolicy-inject.c

clean:
	$(MAKE) -C $(LIBDIR) clean

