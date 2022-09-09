.SUFFIXES: .tex .pdf
.PHONY: celan debs

define WRAP
INPUT_$(1)=$(wildcard $(1)*.tex)
.PHONY: $(1).pdf
all: $(1).pdf

$(1).pdf: $$(INPUT_$(1):%.tex=%.pdf)
$$(INPUT_$(1):%.tex=%.pdf): $$(INPUT_$(1)) heading.tex
	xelatex -shell-escape -interaction=nonstopmode $$<
endef

LECTURES=wildcards

$(foreach i,$(LECTURES),$(eval $(call WRAP,$(i)) ) )

celan: clean
clean:
	@$(RM) -r _minted*
	@$(RM) *.aux *.log *.nav *.out *.snm *.toc *.vrb *.synctex.gz
	$(RM) *.pdf

debs:
	sudo apt install texlive-xetex texlive-fonts-extra texlive-science
