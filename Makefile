all:
	xelatex  induction
	bibtex induction
	xelatex  induction
	xelatex  induction

run:
	/home/gares/COQ/coq/bin/coqide -R /home/gares/LPCIC/coq-elpi/theories elpi -I /home/gares/LPCIC/coq-elpi/src $(F)
