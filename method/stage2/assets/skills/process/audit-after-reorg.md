---
id: audit-after-reorg
layer: process
applies_to: after moving/adding proof files
lib: scripts/check_axioms.sh; scripts/proof_level.py
maturity: promoted
---
# Audit after reorg, not just `lake build`

A green `lake build` is not enough after a file move or bulk add. Run `scripts/check_axioms.sh` (whitelisted-axioms audit, fail-closed, globs the whole `WholeDesign/` dir) AND `scripts/proof_level.py` (level classification). A silent `PKG_DIRS` miss once dropped the audited-theorem count from 2881 to 46 while the build stayed green — the build compiles what it sees, the audit counts what it should. Also delete scratch/experiment files before finishing: a stray unproven theorem in an audited dir fails the audit even if nothing imports it.
