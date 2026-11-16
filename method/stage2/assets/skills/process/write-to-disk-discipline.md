---
id: write-to-disk-discipline
layer: process
applies_to: every proof-authoring session
lib: .claude/skills/leanrtl-full-temporal/SKILL.md (Discipline section)
maturity: promoted
---
# Write to disk, fill one sorry at a time

Write the file to disk EARLY: skeleton + `sorry` for each obligation + imports, then `lake build` the skeleton green, then fill sorries one at a time, rebuilding and saving after each. Never grind arithmetic in a chat buffer — agents finish-file-but-hang and lose everything; the disk is the only source of truth. Land Tier 1 (the mechanical register trace) sorry-free before attempting Tier 2 (the semantic headline); if Tier 2 defeats you, delete its stubs and ship Tier 1 — never leave a `sorry`, never overclaim an unproven Tier 2 in the docstring.
