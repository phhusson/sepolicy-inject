# Installation directories.
PREFIX ?= $(DESTDIR)/usr
INCLUDEDIR ?= $(PREFIX)/include
LIBDIR ?= $(PREFIX)/lib
SHLIBDIR ?= $(DESTDIR)/lib
RANLIB ?= ranlib
LIBBASE ?= $(shell basename $(LIBDIR))
CILDIR ?= ../cil

LIBVERSION = 1

LEX = flex
CIL_GENERATED = $(CILDIR)/src/cil_lexer.c

LIBA=libsepol.a 
LIBMAP=libsepol.map
OBJS= $(patsubst %.c,%.o,$(wildcard *.c))
LOBJS= $(patsubst %.c,%.lo,$(wildcard *.c))
CFLAGS ?= -Werror -Wall -W -Wundef -Wshadow -Wmissing-format-attribute -O2

override CFLAGS += -I. -I../include -D_GNU_SOURCE

ifneq ($(DISABLE_CIL),y)
OBJS += $(sort $(patsubst %.c,%.o,$(wildcard $(CILDIR)/src/*.c) $(CIL_GENERATED)))
LOBJS += $(sort $(patsubst %.c,%.lo,$(wildcard $(CILDIR)/src/*.c) $(CIL_GENERATED)))
override CFLAGS += -I$(CILDIR)/include
endif


all: $(LIBA)


$(LIBA):  $(OBJS)
	$(AR) rcs $@ $^
	$(RANLIB) $@

$(LIBMAP): $(LIBMAP).in
ifneq ($(DISABLE_CIL),y)
	cp $< $@
else
	sed -e '/^\s*cil_/d' < $< > $@
endif

ifneq ($(DISABLE_CIL),y)
$(CILDIR)/src/cil_lexer.c: $(CILDIR)/src/cil_lexer.l
	$(LEX) -t $< > $@
endif

%.o:  %.c 
	$(CC) $(CFLAGS) -fPIC -c -o $@ $<

%.lo:  %.c
	$(CC) $(CFLAGS) -fPIC -DSHARED -c -o $@ $<

clean: 
	-rm -f $(LIBPC) $(OBJS) $(LOBJS) $(LIBA) $(LIBSO) $(TARGET) $(CIL_GENERATED)

