PAPERS := $(patsubst %/Makefile,%,$(wildcard */Makefile))
TARGET ?= dist

all: $(PAPERS)

$(PAPERS):
	$(MAKE) -C $@ $(TARGET)

.PHONY: all $(PAPERS)
