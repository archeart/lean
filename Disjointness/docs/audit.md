# Audit record

## Current scope

This records the completed Phase 1 dependency/interface audit and Phase 2 structural audit. No DISJ lower bound is
claimed. `blueprint.md` contains target statements and candidate constants only.

## Definition review obligations

- Constants precede dimension, seed types, seed laws, and protocols in the quantifiers.
- The protocol never receives the analysis switch vector.
- Correctness covers every input, including intersecting inputs outside the input law's support.
- Public-seed entropy is excluded from the communication charge.
- Local decision functions see only their own augmented inputs and public history.
- Public stopping/next-speaker rules prevent free signaling through control flow.
- A concrete send-input protocol must witness that the model can compute DISJ.
- Leaf counts must come from the tree; arbitrary variable-length strings do not
  have the cardinality bound `2^c`.
- Tree-depth versus reachable cost, finite random-seed normalization, and the
  optional output bit remain explicit proof obligations.

## Axiom checks

`lake lean Audit.lean` passed. The seven checked integration results have exactly
`[propext, Classical.choice, Quot.sound]` as their transitive axioms. `Tree.run`
uses no axioms. The probability-based correctness definition and cost definition
use ordinary foundations only. Full output is in `axioms.log`.

No `sorryAx` or unproved project mathematical axiom occurs in these inspected results.
No `native_decide` was used. This check must be repeated for future results and
especially for the final endpoint. PFR's suppression of `sorry` warnings makes
transitive inspection particularly important.

The printed `FiniteLowerBoundClaim` is **only a target proposition**. Defining or
printing it supplies no proof.

## Phase 2 review

- `sendInputProtocol_correct` supplies an actual correct DISJ protocol in every
  dimension, with `sendInputProtocol_cost = n+1`. The last bit is Bob's answer.
- `Tree.decode_run` proves the public output convention, rather than merely relying
  on an informal interpretation of the tree.
- `Tree.run_transcript_eq_iff` proves locality as a rectangular execution fiber on
  augmented inputs. Factorization then follows by independent private-seed sums.
- `viewLaw_apply` explicitly connects fixed-public-seed execution to the original
  joint seed/transcript law, including zero-mass public seeds.
- The leaf bound is proved by induction on the tree. There is no assumption about
  counting all bit strings shorter than a cost bound.
- `run_length_le_cost` proves transmitted bits are at most the tree-depth cost.
  The converse normalization needed to transfer a lower bound to conventional
  reachable-transcript cost remains open and is not hidden in this theorem.
- Source review found no `sorry`, `admit`, mathematical `axiom`, or `native_decide`
  declaration/tactic. The sole source-text occurrence of `axiom` is the target
  file's explanatory comment.
- Every public Phase 2 theorem was added to `Audit.lean`; all transitive axiom sets
  are subsets of `{propext, Classical.choice, Quot.sound}`. See `axioms.log`.

## Reproduction

Verified on the installed toolchain, with the pinned dependency cache:

```sh
lake clean disjointness
lake --wfail build
lake lean Audit.lean
```

The latest clean build rebuilt the seven project library modules, with no warnings. Build
output is in `clean-build.log`; `build.log` records the latest incremental build after
a documentation-comment update. Preserve `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json` together. Do not run dependency upgrades as part of reproduction.

This is a clean **project** rebuild, not an independent fresh-machine or source-only
rebuild of every dependency. Mathlib artifacts came from its official compiled cache;
the required PFR source modules and this project's proofs compiled locally. Full
reproduction and semantic review remain Phase 7 obligations.
