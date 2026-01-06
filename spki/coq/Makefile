# SPKI TCB - Coq Verification Build
#
# Builds formal proofs of SPKI TCB cryptographic properties.
#
# Usage:
#   make          - Build all Coq proofs
#   make check    - Type-check proofs (fast)
#   make clean    - Remove generated files
#   make html     - Generate HTML documentation

COQMAKEFILE := Makefile.coq

.PHONY: all clean check html

all: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

check: $(COQMAKEFILE)
	@echo "Type-checking Coq proofs..."
	@$(MAKE) -f $(COQMAKEFILE) quick

html: $(COQMAKEFILE)
	@echo "Generating HTML documentation..."
	@$(MAKE) -f $(COQMAKEFILE) html

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) cleanall; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
	@rm -rf html/
	@rm -f *.vo *.vok *.vos *.glob *.aux .*.aux
	@echo "Cleaned Coq build artifacts"

.PHONY: status
status:
	@echo "=== SPKI TCB Coq Verification Status ==="
	@echo ""
	@echo "Proofs implemented:"
	@grep -h "^Theorem\|^Lemma" *.v | wc -l | xargs echo "  Theorems/Lemmas:"
	@grep -h "^Axiom" *.v | wc -l | xargs echo "  Axioms (crypto assumptions):"
	@echo ""
	@echo "Admitted proofs (TODO):"
	@grep -h "Admitted\." *.v | wc -l | xargs echo "  Count:"
	@echo ""
	@echo "Files:"
	@ls -1 *.v
