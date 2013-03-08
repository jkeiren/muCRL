programs=$(patsubst %.c, %, $(wildcard *.c))
.PHONY: all install $(programs)
all install invcheck invelm confcheck reachelm confelm stategraph mcrl2pvs:
	@(cd ../../src; $(MAKE) --no-print-directory -f Makefile libmcrl.a)
	@$(MAKE) --no-print-directory -f Makefile $@

.DEFAULT:
	@$(MAKE) --no-print-directory -f Makefile $@
