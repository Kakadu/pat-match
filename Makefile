.PHONY: unn switch nonlin guards gadt lorry gcw bench

DUNEOPTS=
ifeq ($(VERBOSE),1)
V=
DUNEOPTS+= --verbose
else
V=@
endif

.PHONY: run run-mini celan

all: switch

bench:
	dune build --profile=release switch/main_switch.exe
	sudo cpupower -c 0 frequency-set --governor performance
	PAT_MATCH_REPEAT=10 OCAMLRUNPARAM='s=2200M,h=2200M,b=0' taskset -c 0 _build/default/switch/main_switch.exe -bench

switch:
	dune exec switch/main_switch.exe $(DUNEOPTS)

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
