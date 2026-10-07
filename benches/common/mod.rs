/// Generate a GNU makefile in the style of a hand-written project makefile,
/// with a section of variables, rules and conditionals for each module.
pub fn gnu_makefile(modules: usize) -> String {
    let mut text = String::from(
        "# Generated for benchmarking\n\
         SHELL := /bin/sh\n\
         CC ?= cc\n\
         CFLAGS ?= -O2 -g -Wall\n\
         PREFIX ?= /usr/local\n\
         srcdir := $(dir $(lastword $(MAKEFILE_LIST)))\n\
         \n\
         .PHONY: all clean install check\n\
         \n\
         all: build\n\
         \n\
         -include config.mk\n\
         \n\
         define compile_template\n\
         $(1)_OBJS := $$(patsubst %.c,%.o,$$($(1)_SRCS))\n\
         $(1): $$($(1)_OBJS)\n\
         \t$$(CC) $$(LDFLAGS) -o $$@ $$^ $$($(1)_LIBS)\n\
         endef\n\
         \n",
    );
    for i in 0..modules {
        text.push_str(&format!(
            "# Module {i}\n\
             mod{i}_SRCS = src/mod{i}/a.c src/mod{i}/b.c \\\n\
             \tsrc/mod{i}/c.c src/mod{i}/d.c\n\
             mod{i}_LIBS := -lm $(shell pkg-config --libs glib-2.0)\n\
             mod{i}_CFLAGS += -DMODULE={i} -I$(srcdir)/include\n\
             \n\
             ifeq ($(ENABLE_MOD{i}),yes)\n\
             PROGRAMS += mod{i}\n\
             $(eval $(call compile_template,mod{i}))\n\
             else ifdef FORCE_MOD{i}\n\
             PROGRAMS += mod{i}\n\
             endif\n\
             \n\
             src/mod{i}/%.o: src/mod{i}/%.c src/mod{i}/config.h | build/mod{i}\n\
             \t@echo \"  CC $@\"\n\
             \t$(CC) $(CFLAGS) $(mod{i}_CFLAGS) -c -o $@ $<\n\
             \n\
             build/mod{i}:\n\
             \tmkdir -p $@\n\
             \n\
             check-mod{i}: mod{i}\n\
             \t./mod{i} --self-test > $(@:check-%=%).log 2>&1 || \\\n\
             \t  (cat $(@:check-%=%).log; exit 1)\n\
             \n"
        ));
    }
    text.push_str(
        "build: $(PROGRAMS)\n\
         \n\
         check: $(addprefix check-,$(PROGRAMS))\n\
         \n\
         install: build\n\
         \tinstall -d $(DESTDIR)$(PREFIX)/bin\n\
         \tinstall -m 755 $(PROGRAMS) $(DESTDIR)$(PREFIX)/bin\n\
         \n\
         clean:\n\
         \trm -f $(foreach p,$(PROGRAMS),$($(p)_OBJS)) $(PROGRAMS)\n",
    );
    text
}
