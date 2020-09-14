## 2017-04-20
## Makefile for subdirectory src

all: TAGS .dep.notags


srcs = $(shell ls *.scm)

.dep.notags: minitab.scm

TAGS: $(srcs)
	etags `ls *.scm`

clean:
	rm -rf .dep .dep.*
	rm -rf TAGS
	rm -rf *~ *%
	rm -rf grammar.log

minitab.scm: grammar.scm lalr.scm
	rm -f minitab.scm
	if which scheme > /dev/null; then \
		echo "Using Chez Scheme to build parser..."; \
		scheme grammar.scm > grammar.log; \
	elif which petite > /dev/null; then \
		echo "Using petite to build parser..."; \
		petite grammar.scm > grammar.log; \
	elif which racket > /dev/null; then \
		echo "Using Racket to build parser..."; \
		racket -l mzscheme -l r5rs -f grammar.scm > grammar.log; \
	elif which mzscheme > /dev/null; then \
		if [ -z "`mzscheme -v | sed -e 's/.*Racket.*//'`" ]; then \
			echo "Using mzscheme/Racket to build parser..."; \
			mzscheme -l mzscheme -l r5rs -f grammar.scm > grammar.log; \
		elif [ -z "`mzscheme -v | sed -e 's/.*v4.*//'`" ]; then \
			echo "Using mzscheme (>= v4) to build parser..."; \
			mzscheme -l mzscheme -l r5rs -f grammar.scm > grammar.log; \
		else \
			echo "Using mzscheme (< v4) to build parser..."; \
			mzscheme -f grammar.scm > grammar.log; \
		fi; \
	elif which guile > /dev/null; then \
		echo "Using guile to build parser..."; \
		guile grammar.scm > grammar.log; \
	else \
		echo "Please install either Chez Scheme, Petite Scheme, Racket, MzScheme, or Guile to build the parser!"; \
		false; \
	fi

