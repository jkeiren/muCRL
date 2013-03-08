programs=$(patsubst %.c, %, $(wildcard *.c))
.PHONY: all install install0 withoutsim  $(programs)
.SUFFIXES:
all xsim install:
	@(cd ../prover/src; $(MAKE) --no-print-directory -f Makefile libprover.a)
	@(cd ../prover/src; $(MAKE) --no-print-directory -f Makefile libstategraph.a)
	@$(MAKE) --no-print-directory -f Makefile $@

rewr withoutsim install0:
	@(cd ../prover/src; $(MAKE) --no-print-directory -f Makefile libprover.a)
	@$(MAKE) --no-print-directory -f Makefile $@

.DEFAULT: 
	@$(MAKE) --no-print-directory -f Makefile $@

