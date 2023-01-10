-include Makefile.coq

Makefile.coq: 
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

cleanall:: clean
	rm -f *.d Makefile.coq* 
