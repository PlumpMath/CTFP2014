all : $(patsubst %.lhs,%.pdf,$(wildcard *.lhs))

%.tex: %.lhs
	lhs2TeX -o $@ $?

%.pdf: %.tex
	pdflatex $?

clean:
	rm -f *.tex
	rm -f *.dvi
	rm -f *.pdf
	rm -f *.aux
	rm -f *.ptb
	rm -f *.log

