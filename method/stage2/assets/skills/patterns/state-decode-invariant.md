---
id: state-decode-invariant
layer: pattern
applies_to: pattern / lockout FSMs (L5)
principle: leaf-is-decision-not-induction
tactics: [bv-decide-for-fixed-width, decide-for-finite]
lib: "—"  # transition-table proof is design-local (stateSpec + bv_decide)
example: door_lock (LeanRTL/Designs/CvdpAgentic/DoorLock.lean, stateSpec / stateNext_correct)
maturity: promoted
strike: 3
---
# State-decode invariant

For a controller FSM, do not try to prove behaviour directly over the raw state register; decode the state to a semantic predicate and prove the whole transition table equals a clean `stateSpec`. In `DoorLock.lean`, `stateNext_correct` shows the emitted state cone is exactly `stateSpec` (7-state lockout table), and register cones (`keyOk`, `takeKey`, `lenOk`, `passMatch`) plus scenario "star" theorems (three_strikes, lockout_holds, admin_unlocks) pin the meaning. `bv_decide` closes each finite transition. Gotcha: unlisted spec transitions must be pinned by reading the table as authoritative (e.g. PASSWORD_FAIL's non-lockout successor = IDLE) — the star scenarios validate those inferences against the hidden checker.

## Worked example

```lean
theorem stateNext_correct :
    eval stateNextExpr env =
      stateSpec (env.lookup "state" 3) (env.lookup "srst" 1) (env.lookup "admin_override" 1)
        (env.lookup "admin_set_mode" 1) (env.lookup "w_take_key" 1) (env.lookup "confirm" 1)
        (env.lookup "w_len_ok" 1) (env.lookup "w_pass_match" 1)
        (env.lookup "new_password_valid" 1) (env.lookup "fail_count" 2) := by
  simp only [stateNextExpr, stateSpec, …]
  bv_decide
```
> Source: LeanRTL/Designs/CvdpAgentic/DoorLock.lean:194 (design-local `stateSpec` + `bv_decide`)
