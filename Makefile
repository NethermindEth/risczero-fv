default:
	pdflatex -shell-escape is0.tex
clean:
	rm -f *.aux *.log *.pdf *.idx *.out *.listing
	rm -rf _minted*
view:
	open is0.pdf
