# Fibration categories project makefile.
# Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine, 2012 and onwards.

# Quick usage: “make” to build core of library, “make all” for all modules.

# Based on example given by Adam Chlipala, in “Theorem Proving in the Large”,
# section “Build Patterns”. http://adam.chlipala.net/cpdt/html/Large.html

# Modules to be compiled by default, in plain “make”.
# Includes everything that compiles successfully in reasonable time.
MODULES-CORE := Auxiliary Arith Fundamentals CommutativeSquares Equalizers \
	Pullbacks Pullbacks2 Pullbacks3 Limits1 Limits2 \
	PointedTypes LongExactSequences

# Remaining modules, included only in “make all”.
MODULES-EXTRA := Pullbacks3_alt

VS-CORE  := $(MODULES-CORE:%=%.v)
VS-EXTRA := $(MODULES-EXTRA:%=%.v)

.PHONY: core clean

core: Makefile.coq
	$(MAKE) -f Makefile.coq 

Makefile.coq: Makefile $(VS-CORE)
	coq_makefile -R . "" $(VS-CORE) -o Makefile.coq COQC = hoqc COQDEP = hoqdep

all: Makefile_all.coq
	$(MAKE) -f Makefile_all.coq 

Makefile_all.coq: Makefile $(VS-CORE) $(VS-EXTRA)
	coq_makefile -R . "" $(VS-CORE) $(VS-EXTRA) -o Makefile_all.coq COQC = hoqc COQDEP = hoqdep

clean:: Makefile-core.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile-core.coq