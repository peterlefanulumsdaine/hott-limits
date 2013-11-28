# Fibration categories project makefile.
# Jeremy Avigad, Chris Kapulkin, Peter LeFanu Lumsdaine, 2012.

# The modules to be compiled by default.  
# For these, just call “make” at the commandline.
# For now, includes everything that compiles successfully and in reasonable time; happily, this also includes everything required as a dependency by other files.
default: limits sequences

# All modules (invoked by “make all”).
all: auxiliary arith fundamentals limits-common pullbacks limits pointedtypes sequences twopullbacks twopullbacksalt

# Command to be used for compiling coq files.
# Change this locally if eg “hoqc” doesn’t resolve correctly on your system.
COQC=hoqc

# Specific files involved in each submodule: 
auxiliary:
	$(COQC) Auxiliary.v

arith: auxiliary
	$(COQC) Arith.v

fundamentals: auxiliary
	$(COQC) Fundamentals.v

limits-common: fundamentals
	$(COQC) CommutativeSquares.v Equalizers.v

pullbacks: limits-common
	$(COQC) Pullbacks.v Pullbacks2.v

twopullbacks: pullbacks
	$(COQC) Pullbacks3.v

twopullbacksalt: pullbacks
	$(COQC) Pullbacks3_alt.v

limits: limits-common arith pullbacks
	$(COQC) Limits.v Limits2.v

pointedtypes: pullbacks
	$(COQC) PointedTypes.v

sequences: pullbacks pointedtypes
	$(COQC) LongExactSequences.v

# Call “make clean” to remove all compiled files:
clean:
	rm -rf *.vo *.glob