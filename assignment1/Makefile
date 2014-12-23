all : $(patsubst %.lhs,%.pdf,$(wildcard *.lhs))

%.tex: %.lhs $(wildcard $@*.lhsinclude)
	lhs2TeX -o $@ $<

%.tex: %.lagda
	agda -i. --latex --latex-dir=. $?

%.pdf: %.tex $(wildcard $@*.texinclude)
	latexmk -pdf $*

clean:
	rm -f *.tex
	rm -f *.dvi
	rm -f *.pdf
	rm -f *.aux
	rm -f *.ptb
	rm -f *.log
	rm -f *.out
	rm -f *.agdai
	rm -f *.toc
	rm -f *.blg
	rm -f *.bbl
	rm -f *.fdb_latexmk
	rm -f *.fls

