.PHONY: celan clean all might might-weasel might-passive might-dups

MAIN=main
.PHONY: $(MAIN).pdf clean deps

all: $(MAIN).pdf

OCANREN_TEX=$(MAIN).tex

COMPILER=pdflatex #-interaction=nonstopmode

$(MAIN).fmt: $(wildcard $(MAIN).tex)
	$(COMPILER) -ini -jobname="$(@:.fmt=)" "&$(COMPILER)" mylatexformat.ltx $<

$(MAIN).pdf: $(OCANREN_TEX) $(MAIN).fmt
	$(COMPILER) -fmt=$(MAIN).fmt -interaction=nonstopmode $<
	bibtex $(MAIN).aux
	$(COMPILER) -fmt=$(MAIN).fmt -interaction=nonstopmode $<
	$(COMPILER) -fmt=$(MAIN).fmt -interaction=nonstopmode $<

celan: clean
clean:
	$(RM) -f *.synctex.gz *.bak *.out *.aux *.bbl *.blg *.log $(MAIN).pdf 

deps:
	sudo apt install texlive-fonts-extra

might: might-weasel might-passive might-dups
might-weasel:	
	echo "weasel words: "
	sh ../bin/weasel *.tex
	echo

might-passive:	
	echo "passive voice: "
	sh ../bin/passive *.tex
	echo

might-dups:	
	echo "duplicates: "
	perl ../bin/dups *.tex
	echo
