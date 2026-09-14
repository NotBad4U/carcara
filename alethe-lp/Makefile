# Explicit rather than recursive: generated proofs live in proofs/ (see
# scripts/translate-benchmarks.sh) and must not be swept into the build.
SRC := $(wildcard *.lp rare/*.lp)
OBJ := $(SRC:%.lp=%.lpo)

default: $(OBJ)

# One lambdapi invocation per module: `lambdapi check -c` compiles the
# dependencies on demand, and checking every file in a single process trips
# the .lpo loader on modules that carry string literals (see Tactic.lp).
%.lpo: %.lp
	lambdapi check -c -v 0 -w $<

clean:
	rm -f *.lpo rare/*.lpo

install: $(OBJ)
	lambdapi install lambdapi.pkg $(SRC) $(OBJ)

uninstall:
	lambdapi uninstall lambdapi.pkg
