-include Makefile.coq

Makefile.coq: 
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq -docroot PartialOrders

cleanall:: clean
	rm -f *.d Makefile.coq* */*.glob */.*.aux */*.vo*

justlib:: theories/chain.vo theories/adjunctions.vo

sanity:: tests/sanity.vo
