# RTL → LeanRTL frontend

`import_refinement.py` provides the import-only entry point. `importer.py` / `symbolic.py` handle Yosys RTLIL; `clocked.py` / `system.py` / `timed.py` / `fourstate.py` handle their respective semantics; `native_memory.py` preserves actual native RAM. `pipeline.py` supports local conversion and optional roundtrip checks. `tests/`, `proofs/`, and `templates/` contain general regressions and supporting resources.

```bash
python3 -m v2lean.import_refinement --help
python3 -m unittest discover -s method/stage2/v2lean/tests -v
```

Some tests require Yosys, Icarus, built Lean libraries, or optional pyslang. Remote Jasper tools are used only when their workflows are explicitly invoked; no remote verification was run during packaging.

Bulk corpus inputs, historical runs, coverage tables, and their experiment drivers were not migrated. Successful import and structural checks do not establish functional refinement. Functional proving is in `method/stage2/refinement/`; the complete native-memory example is in `case_cpu/memory/`.

Compatibility repair: the old MemBlock roundtrip `describe/cut_memories/NativeImporter` API and the newer CPU `NativeMemoryImporter` originally shared a filename. Replacing the former with the latter broke older imports. This package restores the archived implementation as `memblock_compat.py` and updates the legacy imports. The CPU native-memory importer itself is unchanged; the two semantics and acceptance criteria remain separate.
