IDRIS2 ?= idris2
INTERACTIVE ?= --interactive
NJOBS ?= $(shell (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 1)
threads ?= $(NJOBS)
TRGT = daitests

.PHONY: testbin test

test:
	./build/exec/$(TRGT) $(IDRIS2) $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only $(only) --except $(except)

retest:
	./build/exec/$(TRGT) $(IDRIS2) $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only-file failures --only $(only) --except $(except)

testbin:
	${IDRIS2} --build $(TRGT).ipkg

clean:
	$(RM) failures
	$(RM) -r build
	$(RM) -r **/**/build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
