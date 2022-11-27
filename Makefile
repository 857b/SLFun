INVOKE := @$(MAKE) --no-print-directory -f CoqMakefile

all: CoqMakefile
	$(INVOKE)

%.vo: CoqMakefile FORCE
	$(INVOKE) $@

clean: CoqMakefile
	$(INVOKE) clean
	@rm CoqMakefile CoqMakefile.conf

CoqMakefile: Makefile _CoqProject
	@echo "MAKEFILE"
	@coq_makefile -f _CoqProject -o CoqMakefile

.PHONY: all clean FORCE
FORCE:
