export TEXINPUTS:=$(TEXINPUTS)

FILE := proof

pdf: $(FILE).tex
	pdflatex $(FILE).tex && bibtex $(FILE).aux && pdflatex $(FILE).tex && pdflatex $(FILE).tex

clean:
	rm *.pdf *.log *.aux *.out *.bbl *.blg *-blx.bib *.run.xml

