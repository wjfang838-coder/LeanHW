# Hard rules for authoring

Violating any of these voids the run. Rules 1–6 are the isolation and deliverable rules;
7–9 are the **adjudication discipline**, added 2026-08-06 after measuring what actually
went wrong (see `docs/findings/`).

## Isolation and deliverable

1. **All building and verification goes through the harness entry point**
   (`build` / `audit` / `check` / `sim` / `cosim` / `emit` / `paramcheck`).
   Never invoke `lake`, `lean`, `leanrtl` or `yosys` directly on the design.
2. **File ownership.** You may create or modify only your own design file, your own notes
   file, and your own scratch directory. Nothing else.
3. **Do not read**: another design's files, specs, notes or logs; anything under the
   harness's output directories that is not yours; **any path outside the workspace**.
   No network.
4. Keep the scaffold's four section markers intact — the harness keys on them.
5. **Zero `sorry` / `admit` / new axioms.** A proof that does not close is not a deliverable.
6. The emitted module name and every port name and width must match your spec exactly.
   The grading testbench instantiates by name and you will never see it.

## Adjudication discipline

### 7. Adjudicate only from the spec text

When the spec leaves something open you must choose, and you record the choice. But the
*reason* may cite only:

- **(a)** a verbatim quote from your spec,
- **(b)** an arithmetic or logical consequence of such a quote, or
- **(c)** an explicitly-labelled convention (e.g. "the usual ready/valid handshake"),
  stated *as a convention* and never as a fact about the grader.

**You have never seen the reference implementation.** Any sentence of the form
"the reference does X" / "the golden RTL is shaped like Y" / "the grader's design has the
same transient" is a **fabrication about an object you cannot observe**, and is not a reason.
If you catch yourself writing one, delete it and re-decide from the text.

> **Why this rule exists.** Three designs failed with this exact signature: a spec sentence
> was read correctly, written into the notes as the natural reading, and then *overruled by an
> invented reference*. In one case the notes named the correct reading and rejected it, citing a
> golden-RTL shape that does not exist. **The information was in hand and was discarded.**
> Two of the three passed on re-authoring under this rule.

### 8. A stated top-level property is a proof obligation, not commentary

If the spec states a whole-design property — a division ratio, a period, a latency, a
throughput, an algebraic law the outputs satisfy, a durations table — **in addition to** a
mechanism, formalise **both** and prove they agree.

If your implementation cannot satisfy the stated top-level property, **you have the wrong
implementation**. Do not ship it with a note conceding the discrepancy.

Two descriptions of one thing is the spec handing you a free consistency check. Use it.

> **Why this rule exists, and that it works.** In one design the spec gave both a state-machine
> mechanism and a table of phase durations; the two candidate readings of the mechanism differ by
> one cycle per phase, and **the durations table decides between them**. The author proved the
> durations rather than asserting them, and the design passed. In another, a flag was stated as a
> *property* in the port table and as a *mechanism* in the body; formalising both and proving they
> coincide refuted the reading that had failed a previous run.
>
> The converse is the warning: one author shipped an implementation whose measured behaviour
> contradicted the ratio its spec stated, with a note conceding the discrepancy. It knew, and
> shipped anyway.

**8a. When the two descriptions cannot both hold, do not let the property overrule the
mechanism — record the conflict and hand it back.**

Rule 8 works because two descriptions of one thing check each other. It assumes both are true of
the design you are being asked to build. Where the spec is documentation written *about* an
existing implementation, that assumption fails: prose drifts from code, and the sentence that
drifts is almost always the *asserted property*, not the *executable mechanism*.

So when a stated property and a stated mechanism are irreconcilable:

* implement the **mechanism**, at the widths and in the arithmetic the spec actually writes;
* state the conflict explicitly in your notes, with the input on which the two disagree;
* do **not** silently adopt the property and call the mechanism a misprint.

You are allowed to believe the property is what was meant. You are not allowed to act on that
belief without saying so.

> **Why this sub-rule exists.** A FIFO spec gave `mem_empt` as a mechanism —
> "determined by … (`adr_i - adr_o`)", port width 6, pointers 4 bits — and as a property: §8.2
> "verify that `mem_empt` correctly indicates a full FIFO". Verilog evaluates that subtraction at
> the assignment width, so on a full FIFO straddling a wrap (`adr_i=0`, `adr_o=8`) the reference
> emits **56**, not 8. The property is simply false of the design it describes.
>
> The author found the fork, computed the 56, and rejected the six-bit reading *because* §8.2
> refuted it — following rule 8 exactly as written. Every other port on that design was right;
> `mem_empt` was the only one wrong, 2548 mismatches. Rule 8c had already removed three other
> ports' worth of errors on the same design. **Rule 8, unqualified, put this one back.**
>
> The differential is in `runs.bak.2026-08-12/_repair/MemEmpt.lean`: the readings separate at `adr_i=0,
> adr_o=1` and `ref_violates_8_2` is a one-line `decide`.

### 8b. Discharge an observable clause against the observable trace, not against a helper

Rule 8 tells you to formalise a stated property. This one tells you *what it has to be a
property of*. If the spec constrains what can be **seen at a port at a cycle**, the theorem must
be about the port at that cycle — `outputs?eval` on the real trace. A theorem about the internal
function that feeds the port is a different claim, and the two come apart exactly when your
reading of the timing is wrong.

The test: can your theorem still be true while the module's pins violate the clause? If yes, you
have not discharged it.

> **Why this rule exists.** A spec said, under *Corner Cases*: "When `rcnt>9`, output should be
> `0x00000000`". The author cited that clause **eight times**, wrote a known-answer test for it,
> and the test passed — it proved that the ROM function `rcon` returns 0 at indices 10 and 11.
> True, and about the wrong object. The design decoded the ROM with the *pre-edge* counter, so on
> the cycle where `rcnt` reads 10 the pin `out` read `0x36000000`. 613 of 795 samples mismatched.
>
> Nothing else caught it: 24 theorems, full `Refines` observed at the pin over arbitrary input and
> reset streams, `#print axioms` clean apart from `bv_decide`, every gate green. The machinery to
> state the real obligation was already in the file — `aes_rcon_observe` connects the pin to the
> trace — and `∀ t, rcnt t > 9 → out t = 0` would not have proved.
>
> The failure mode is worse than an omission: the clause that should have **refuted** the reading
> was absorbed as a clause **confirming** it, because under the wrong reading it is also true of
> some component. Going looking for evidence is not enough; the evidence has to be about the pins.

### 8c. Do not add state or gating the spec does not describe

Every register, every enable, every qualification of one signal by another is a claim about the
design. If the spec does not put it there, do not put it there. A holding register "so the data
stays valid", a `ready` qualified by the requester's own `valid`, a write-enable qualified by a
chip-select — each of these is defensible engineering and each is a *different circuit* from the
one specified.

When the spec names a signal's meaning, implement that meaning and nothing more. "Ready" that
depends on the master's own request is not readiness. If you believe the specified circuit is
wrong, say so in your notes and build the specified one anyway.

> **Why this rule exists.** One design failed on exactly three deviations, all invented: `ready`
> gated by the master's own `valid`, a read-data holding register the prompt never mentions, and
> `we` gated by `cs`. The port table said "Indicates that the DTCM is ready to accept the command
> from the LSU" and the body said read data "is extracted via `dtcm_ram_dout` and returned to the
> response channel" — a straight-through path with no holding stage.
>
> The control that removes every excuse: the **vanilla** arm read a byte-identical prompt and got
> all three right. Fixing only these three deviations reproduced vanilla's profile exactly
> (84/222 mismatches); fixing everything gave 0/222. The prompt was adequate; the additions were
> not asked for.

### 9. Refuse when the spec cannot determine the interface

If the spec is missing, truncated, or otherwise insufficient to fix the module name, the port
list, or the port widths, **stop and report the blocker**. Do not reconstruct a contract from
surrounding metadata, from the design's name, or from recollection of a similarly-named public
design.

Authoring against an invented contract produces a green-looking artifact that measures
memorisation rather than specification-following, and self-certifies: co-simulation only checks
your Lean semantics against your own emitted Verilog, so a wrong interface passes every local
gate and fails only at grading.

> **Why this rule exists.** A dispatch error once sent three agents to a workspace holding
> neither their specs nor their scaffolds. Two refused and reported the blocker — one of them
> spelling out exactly the reasoning above, unprompted. The third reconstructed a contract from
> a stale manifest row and authored against it, claiming a full refinement proof. All three
> behaviours came from the same instructions; this rule makes the correct one mandatory.

## Recording adjudications

For every adjudicated ambiguity your notes must give **four** things:

| | |
|---|---|
| **Quote** | the verbatim spec text — or an explicit "no section states X" |
| **Chosen** | the reading you took |
| **Rejected** | the alternative(s) you did not take |
| **Blast radius** | which outputs and which cycles the choice affects |

A reason that cannot point at spec text is not admissible (rule 7). An ambiguity whose blast
radius you cannot state is one you have not finished analysing.

These records are the input to `clarify/` — they become machine-readable assumptions, and the
questions put to a human when clarification is available. Prose that a human must read to
recover them is not enough: on one benchmark **19 of 19** failing designs had recorded the
decisive ambiguity in advance, and every one of those records went unread until after grading.
