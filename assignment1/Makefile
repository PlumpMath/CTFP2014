all : $(patsubst %.lhs,%.pdf,$(wildcard *.lhs))

%.tex: %.lhs $(wildcard $@*.lhsinclude)
	lhs2TeX -o $@ $<

%.tex: %.lagda
	agda -i. --latex --latex-dir=. $?

%.pdf: %.tex $(wildcard $@*.texinclude)
	latex $<
	pdflatex $<

RemoveDuplicates.pdf:: RemoveDuplicates.tex
	latexmk -pdf RemoveDuplicates


clean:
	rm -f `cat ../.gitignore`

