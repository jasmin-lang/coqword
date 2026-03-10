# -*- Makefile -*-

# --------------------------------------------------------------------
DUNEOPTS ?=
DUNE     := dune $(DUNEOPTS)

# --------------------------------------------------------------------
.PHONY: default build clean

default: build

build:
	$(DUNE) build

clean:
	$(DUNE) clean
	rm -f src/.lia.cache src/.nia.cache
