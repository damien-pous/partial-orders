KNOWNTARGETS := CoqMakefile sanity justlib
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -docroot . -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

cleanall:: clean
	rm -f CoqMakefile* *.d *.log */*.glob */.*.aux */*.vo*

justlib: theories/gfp.vo theories/instances.vo

sanity: tests/sanity.vo

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
