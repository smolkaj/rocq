.PHONY: all clean

all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

Makefile.rocq: _CoqProject $(wildcard *.v)
	rocq makefile -f _CoqProject -o Makefile.rocq

clean:
	if [ -f Makefile.rocq ]; then $(MAKE) -f Makefile.rocq cleanall; fi
	rm -f Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d
