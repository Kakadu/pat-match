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
	dune build switch/main.exe
	_build/default/switch/main.exe -bench


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
	dune exec switch/demo3.exe $(DUNEOPTS)

nonlin:
	dune exec nonlinear/main_nonlinear.exe $(DUNEOPTS)


lorry:
	dune exec lorry/lorry_run.exe $(DUNEOPTS)


gcw:
	dune exec GCW/GCW_run.exe $(DUNEOPTS)

celan: clean
clean:
	$(RM) -r _build
