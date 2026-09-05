# Generated builds are intentionally avoided: this wrapper works with GNU make
# on Windows and delegates dependency tracking to coq_makefile.

COQMAKEFILE := CoqMakefile

.PHONY: all clean distclean check

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) all

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

check: all
	coqchk -silent -Q theories Janji Janji.FilesystemOracle Janji.Safety Janji.Examples \
	  Janji.one_step_agentic_provenance_and_authority_confinement Janji.trace_safety

clean:
	@rm -f theories/*.vo theories/*.vos theories/*.vok theories/*.glob
	@rm -f theories/*.aux theories/.*.aux .Makefile.d .*.d .lia.cache

distclean: clean
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
