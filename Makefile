DUNEOPTS=
ifeq ($(VERBOSE),1)
V=
DUNEOPTS+= --verbose
else
V=@
endif

.PHONY: run run-mini celan

all: nonlin unn #guards


run:
	dune exec ./main2.exe $(DUNEOPTS)

gadt:
	dune exec ./main_gadt.exe $(DUNEOPTS)

guards:
	dune exec ./main_guards.exe $(DUNEOPTS)

run-mini:
	dune exec mini/minirun.exe $(DUNEOPTS)

unn:
	dune exec ./main_unnested.exe $(DUNEOPTS)

nonlin:
	dune exec ./main_nonlinear.exe $(DUNEOPTS)

celan: clean
clean:
	$(RM) -r _build


