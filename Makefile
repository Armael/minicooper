%: Makefile.coq
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: ;

Makefile: ;

.PHONY: all clean
