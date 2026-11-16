# Profiles

One file, one arm. A profile is the whole of a run's configuration that is not the design: who
authors, what they are given, and which gates decide whether the result counts.

`common/profiles.py` loads them and stamps the name **and a hash of the file's bytes** into every
workspace staged under it; `common/provenance.require` refuses a workspace whose stamp
contradicts the profile it is being run under.

## Never edit a profile in place

Add a file instead. Editing one leaves every artifact of the previous round stamped with a name
that has come to mean something else — a silent change to the meaning of data already collected,
which is the one thing this mechanism exists to prevent. That is also why the hash covers the raw
bytes rather than the parsed object: a comment in a profile is part of the argument for why the
arm is what it is, and two arms that differ only in their justification are not the same arm.

## There is no arm table

The set of arms is exactly the set of `*.yaml` files here. Nothing enumerates them. The tree this
method comes from held ~40 profiles alongside a launcher with a hard-coded `ARMS` dict, so
adding an arm meant editing the launcher and the two lists drifted.

## Fields

| field | meaning |
|---|---|
| `name` | must equal the filename. Both get cited as the arm's identity; if they disagree there is no way to tell which a reader meant. |
| `description` | one paragraph: what this arm *is*, in terms a reader of a results table needs. |
| `authoring` | `two-author` (S writes the spec, it freezes, D implements and proves) · `single` (one author writes all four sections) · `direct-verilog` (no Lean at all) |
| `assets` | named sets from `assets/MANIFEST.yaml`. Nothing else reaches the workspace. |
| `rules` | documents from `assets/instructions/` copied in as authoring rules. |
| `gates` | what "all gates green" means for this arm. See below. |
| `max_spec_versions` | how many times D may challenge the specification before the design is reported as unresolved. |

## Write down every gate, including the ones that always run

`leanrtl/verify.py` runs `builds` and `proves_impl` unconditionally and folds both into
`all_pass`, so they are enforced whether or not a profile lists them. `gates:` is what a reader
consults to learn what a green row *means*, so a list that is a subset of what runs invites
exactly one mistake: reading a green row as "no sorry, no stray axiom, no undriven net" when it
also means "this file elaborates, and states at least one theorem about `impl`".

`proves_impl` in particular is not redundant with the others. `zero_sorry` and `axiom_clean` are
properties of the proofs that *exist*; neither is violated by a file containing no theorem about
the implementation at all. Without it, the false-positive cell of a proof confusion matrix fills
up with designs where there was no guarantee to be false.

A gate's **absence** is a property of the arm too, and a real one: `simdiff` cannot run on a
`single` arm because there is one author and nothing to diff.
