---
id: reset-family-convention
layer: process
applies_to: every sequential design's reset
lib: docs/instructions/CORE.md §2.2
maturity: promoted
---
# Reset family convention (async ⇒ fold in-band **and** `$adff`)

If the NL says the reset is ASYNCHRONOUS (`always @(posedge clk or negedge rst_n)` / "asynchronous reset"), fold it in-band **and** declare it. These are complements, not alternatives:

1. Fold it in-band into every register's `next`, exactly as for a synchronous reset — `.mux (.eq (.var "rst_n" 1) (.const 0)) <resetVal> <normal>`.
2. **On top of that**, give each register `asyncReset := some ("<rstPort>", <activeHi>, <resetVal>)`, naming the **reset port itself** together with its polarity: active-low `rst_n` is `some ("rst_n", false, 0)`, active-high `rst` is `some ("rst", true, 0)`. The port name, polarity and reset value must match the fold's three, signal for signal.

The fold buys the theorem its reset-active edges; the declaration buys the Verilog its `negedge rst_n`. Write only the fold and the testbench fails (the emit is a bare `@(posedge clk)`); write only the declaration and the whole-design theorem is scoped to the reset-inactive segment. Write both and you lose nothing.

**When the spec does not say which style it is, default to ASYNCHRONOUS.** This is the common case — the spec writes only "reset is active low", or just lists an `rst_n` port, and never uses the word "asynchronous". The bet is one-sided: reference RTL for an active-low reset is almost always `always @(posedge clk or negedge rst_n)`, and testbenches routinely deassert reset in the same timestep as a clock edge, where a synchronous reset simply does not take and the whole trace runs late or stays X. In the other direction, an async reset agrees cycle-for-cycle with a sync one under the ordinary "hold reset across at least one edge, then release" stimulus; they diverge only if the stimulus pulses reset strictly between two edges, which is rare.

**Choosing async costs no theorem when you also fold.** `Module.step`/`Module.simulate` never read `Reg.asyncReset`, and `Module.eraseArst_simulate` proves `m.simulate = m.eraseArst.simulate` outright, so the whole-design theorem you would have written for the synchronous twin is verbatim a theorem about your design. Declared-but-not-folded, it is scoped to the reset-inactive segment. Folded as well — `Module.arstFoldedb` reads true — `Reg.arstFolded_arstDen` proves the `$adff`'s denotation *is* the plain next-state, so the cycle model already computes the reset value on a reset-active edge and **nothing is scoped away but the response between edges**. `coveredModuloArst_moduleChecks` hands you the M6 `moduleChecksb` gate from two `by decide` facts. `semanticCoverage` still reports `.asyncReset` (the reset *edge* really is out of model, covered per register by `Reg.arstDen`), and `leanrtl check` now prints which of the two cases you are in. **Never downgrade a reset to synchronous in order to "regain" a theorem** — there is nothing to regain, and the downgrade fails the testbench.

**Do NOT build an inverter wire** (`nrst = ~rst_n`) and declare the reset active-high over it. The emitter writes the declared polarity straight into the sensitivity list and the branch test (`always @(posedge clk or negedge rst_n)` / `if (!rst_n)`); an inverter net instead puts a continuous assign between the port and the flop, and that extra delta loses the race against a testbench that deasserts reset in the same timestep as a clock edge — the whole trace then runs one cycle late. (Measured: this one indirection alone turned a wholly-failing design into a wholly-passing one.) Stop at the in-band fold *alone* — no `asyncReset` declaration — ONLY for a reset the spec states is synchronous. A sync-reset design fails whenever the testbench releases reset on the first clock edge — the registers never clear and stay X. Do not bet a synchronous reset catches the first posedge. (Never combine `asyncReset` with `asyncLoad` on one register — CORE §1.3.) For the trace theorem available when the reset is declared but *not* folded, see pattern `asyncreset-value-trace`.
