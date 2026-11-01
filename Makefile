KNOWNTARGETS := RocqMakefile
KNOWNFILES   := Makefile _RocqProject

.DEFAULT_GOAL := invoke-rocqmakefile

# use the rocq-package option if rocq version supports it
PACKAGE_NAME = rocq-partial-orders
ROCQPKG := $(shell if rocq makefile --no-rocq-package-warning -v >/dev/null 2>&1; then echo "--rocq-package $(PACKAGE_NAME) --legacy-support"; fi)

RocqMakefile: Makefile _RocqProject
	$(ROCQBIN)rocq makefile -f _RocqProject $(ROCQPKG) -o RocqMakefile

invoke-rocqmakefile: RocqMakefile
	$(MAKE) --no-print-directory -f RocqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-rocqmakefile $(KNOWNFILES)

cleanall:: clean
	rm -f RocqMakefile* *.d *.log */*.glob */.*.aux */*.vo*

# This should be the last rule, to handle any targets not declared above
%: invoke-rocqmakefile
	@true

