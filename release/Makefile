# Builds con-pastel's checker executable with the ORIGINAL CakeML compiler.
#
#   make            # build/con-pastel  (the checker)
#   make test       # run it on con-leche's end-to-end fixtures
#   make check-sexp # check that cake parses exactly the emitted program
#
# Pipeline:
#   1. build/con-pastel.sexp : Lean checks conPastel_correct, then prints the
#      proved CakeML program (release/Emit.lean) as an S-expression;
#   2. build/cake            : the CakeML compiler, release $(CAKE_VERSION),
#      downloaded and checked against its SHA-256;
#   3. build/con-pastel.S    : cake compiles the S-expression to x86-64;
#   4. build/con-pastel      : the assembly linked with con_pastel_ffi.c.
#
# Memory: step 1 needs the full Lean build (hours, see README); step 3 runs
# cake with a $(CAKE_HEAP) MiB heap (about 3 minutes).

CAKE_VERSION = v3479
CAKE_SHA256  = e110bfcba19d6524ee4748608a67a275647445a048928cf623c2c9a973e31c9a
CAKE_URL     = https://github.com/CakeML/cakeml/releases/download/$(CAKE_VERSION)/cake-x64-64.tar.gz
CAKE_HEAP   ?= 30000
CAKE_STACK  ?= 8000
CAKEFLAGS    = --sexp=true --exclude_prelude=true --skip_type_inference=true

CC     ?= cc
CFLAGS ?= -O2
B       = build
ROOT    = ..

all: $(B)/con-pastel

$(B):
	mkdir -p $(B)

# 1. The proved program as an S-expression.
$(B)/con-pastel.sexp: Emit.lean | $(B)
	cd $(ROOT) && ulimit -s 8388608 && lake build ConPastel.Leche.Program Flapjack.CakeParser.ToSexp
	cd $(ROOT) && ulimit -s 8388608 && \
	  CON_PASTEL_SEXP=release/$@.tmp lake env lean --tstack=8388608 release/Emit.lean
	mv $@.tmp $@

sexp: $(B)/con-pastel.sexp

# 2. The original CakeML compiler.
$(B)/cake-x64-64.tar.gz: | $(B)
	curl -fsSL -o $@.tmp $(CAKE_URL)
	echo "$(CAKE_SHA256)  $@.tmp" | sha256sum -c -
	mv $@.tmp $@

$(B)/cake: $(B)/cake-x64-64.tar.gz
	tar -xzf $< -C $(B)
	$(MAKE) -C $(B)/cake-x64-64 cake
	cp $(B)/cake-x64-64/cake $@

cake: $(B)/cake

# 3. Compile with cake. Type inference is skipped: the translated program
#    is untyped (see README, "What is trusted").
$(B)/con-pastel.S: $(B)/con-pastel.sexp $(B)/cake
	CML_HEAP_SIZE=$(CAKE_HEAP) CML_STACK_SIZE=$(CAKE_STACK) \
	  $(B)/cake $(CAKEFLAGS) < $< > $@.tmp
	mv $@.tmp $@

# Cross-check of step 1: the original cake prints back (with HOL4's
# print_sexp) the program it parsed; it must be byte-for-byte the emitted
# file. cake writes a newline, then the program, to stderr.
check-sexp: $(B)/con-pastel.sexp $(B)/cake
	CML_HEAP_SIZE=$(CAKE_HEAP) CML_STACK_SIZE=$(CAKE_STACK) \
	  $(B)/cake $(CAKEFLAGS) --print_sexp < $< > /dev/null 2> $(B)/printed.sexp.tmp
	tail -c +2 $(B)/printed.sexp.tmp | cmp - $<
	rm $(B)/printed.sexp.tmp
	@echo "check-sexp: cake parsed exactly the emitted program"

# 4. Link.
$(B)/con-pastel: $(B)/con-pastel.S con_pastel_ffi.c
	$(CC) $(CFLAGS) -o $@ $(B)/con-pastel.S con_pastel_ffi.c

test: $(B)/con-pastel
	./test.sh $(B)/con-pastel

clean:
	rm -rf $(B)

.PHONY: all sexp cake check-sexp test clean
