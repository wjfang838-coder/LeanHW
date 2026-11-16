"""Literal scope certificates for large generated Lean kernel checks.

The tables are not trusted: rfl proves each equal to the actual Module's
declarations. Rewriting with these equalities avoids repeatedly rebuilding
scope lists while the kernel evaluates name and width checks.
"""
from .importer import lean_string


def render(importer):
    use_maps = len(importer.wires) >= 1024
    def table(name, entries):
        return f"def {name} : List (String × Nat) := [" + ", ".join(
            f"({lean_string(n)}, {w})" for n, w in entries) + "]\n"

    regs = [(s["register"], s["width"]) for s in importer.states if s["type"] != "$dlatch"]
    latches = [(s["register"], s["width"]) for s in importer.states if s["type"] == "$dlatch"]
    base = list(reversed(importer.inputs + regs + latches))
    wires = list(reversed([(n, e.width) for n, e in importer.wires]))
    full = wires + base
    text = table("lintBase", base) + table("lintFull", full)
    text += "def lintNames : List String := [" + ", ".join(lean_string(n) for n, _ in full) + "]\n"
    text += """theorem lintBase_eq : impl.baseNameWidths = lintBase := by rfl
theorem lintFull_eq : impl.allNameWidths = lintFull := by rfl
theorem lintNames_eq : lintFull.map (·.1) = lintNames := by rfl
example : impl.checkErrors = [] := by
  simp only [Module.checkErrors, lintBase_eq, lintFull_eq, lintNames_eq]
  decide +kernel
"""
    subject = "transitionView" if importer.latches else "impl"
    width_base = (list(reversed(importer.inputs + [(s["register"], s["width"]) for s in importer.states]))
                  if importer.latches else list(reversed(importer.inputs + regs)))
    text += table("widthBase", width_base) + table("widthFull", wires + width_base)
    text += f"""theorem widthBase_eq : CheckWidth.setupWidths {subject} = widthBase := by rfl
theorem widthFull_eq : CheckWidth.fullWidths {subject} = widthFull := by rfl
"""
    if importer.latches or not importer.coverage_reasons:
        target, unfold = f"CheckWidth.moduleChecksb {subject}", "CheckWidth.moduleChecksb"
    else:
        target, unfold = "impl.wellWidthedb", "Module.wellWidthedb"
    text += f"""example : {target} = true := by
  simp only [{unfold}, widthBase_eq, widthFull_eq]
  decide +kernel
"""
    if use_maps:
        # Every theorem still concludes the original checker proposition.
        # The map versions have kernel-checked equality theorems for all modules,
        # including malformed modules, and only reduce lookup cost.
        text = text.replace("  simp only [Module.checkErrors,",
                            "  rw [← Module.checkErrorsMap_eq]\n  simp only [Module.checkErrorsMap,")
        text = text.replace("  simp only [Module.wellWidthedb,",
                            "  rw [← CheckWidth.wellWidthedbMap_eq]\n  simp only [CheckWidth.wellWidthedbMap,")
        text = text.replace("  simp only [CheckWidth.moduleChecksb,",
                            "  rw [← CheckWidth.moduleChecksbMap_eq]\n  simp only [CheckWidth.moduleChecksbMap, CheckWidth.wellWidthedbMap,")
    return text
