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
	rm -f src/.lia.cahe src/.nia.cache
