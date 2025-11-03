.PHONY: unn switch nonlin guards gadt lorry gcw bench

DUNEOPTS=
ifeq ($(VERBOSE),1)
V=
DUNEOPTS+= --verbose
else
V=@
endif

.PHONY: run run-mini celan

all: switch #nonlin unn #guards

bench:
	dune build switch/main_switch.exe
	_build/default/switch/main_switch.exe -bench


run:
	dune exec ./main2.exe $(DUNEOPTS)

gadt:
	dune exec gadt/main_gadt.exe $(DUNEOPTS)

guards:
	dune exec guards/main_guards.exe $(DUNEOPTS)

run-mini:
	dune exec mini/minirun.exe $(DUNEOPTS)

unn:
	dune exec unn/main_unnested.exe $(DUNEOPTS)

switch:
	dune exec switch/main_switch.exe $(DUNEOPTS)

nonlin:
	dune exec nonlinear/main_nonlinear.exe $(DUNEOPTS)


lorry:
	dune exec lorry/lorry_run.exe $(DUNEOPTS)


gcw:
	dune exec GCW/GCW_run.exe $(DUNEOPTS)

celan: clean
clean:
	$(RM) -r _build

.PHONY: odig
ODIG_SWITCHES = --odoc-theme=odig.gruvbox.light
ODIG_SWITCHES += --no-tag-index
ODIG_SWITCHES += --no-pkg-deps
odig:
	dune install $(DFLAGS) pat-match
	odig odoc $(ODIG_SWITCHES) pat-match

.PHONY: coverage
TEST_COV_D ?= /tmp/pat-match-cov
coverage:
	if [ -d $(TEST_COV_D) ]; then $(RM) -r $(TEST_COV_D); fi
	mkdir -p $(TEST_COV_D)
	BISECT_FILE=$(TEST_COV_D)/GT dune runtest switch \
		--no-print-directory \
		--instrument-with bisect_ppx --force
		bisect-ppx-report html --coverage-path $(TEST_COV_D) #--expect switch/
		bisect-ppx-report summary --coverage-path $(TEST_COV_D) #--expect switch/
