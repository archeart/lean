# Experiment log

## 2026-10-14 — Phase 1 begins

- Start: 2026-10-14 06:37:29 UTC (02:37:29 America/New_York).
- User intervention: installed elan using the supplied command, then reported success.
- Verified host: Apple Silicon macOS; Git 2.50.1 and Apple clang 17 available.
- Elan 4.2.4 present; no installed toolchains at start.
- Initial weekly quota snapshot: 3% used, 97% remaining, account-wide, seven-day
  window. Concurrent usage unknown; this is not exact per-project consumption.
- User-reported model/effort: GPT-6 Astra / xhigh. One agent.
- Sandbox GitHub DNS access failed. The approved network escalation succeeded;
  no user troubleshooting was needed.
- Downloaded PFR at `4c56de547b2f33b0bc47b92f3bfbcebc6457a776`.
- Started installing its matching Lean v4.35.0-rc4 toolchain.

## 2026-10-14 — Phase 1 completed

- Checkpoint: 06:50:43 UTC (02:50:43 America/New_York), about 13 minutes after start.
- Lean installed; Lake resolved all dependencies to the pinned manifest.
- Mathlib's automatic cache hook downloaded and decompressed 9014 artifacts.
  The imported PFR entropy modules were compiled locally.
- Seven integration results compile, including conditional subadditivity and the
  `c * log 2` bound for fixed-length bit-vector alphabets.
- Protocol definitions and the finite-model target proposition compile.
- Initial repairs: made tree recursion structurally explicit; replaced `Π` (a Lean
  syntax token) with an ordinary identifier; adopted the dependency's module system;
  removed unused typeclass assumptions and corrected doc-comment/`omit` placement.
  The first entropy proof bodies compiled without mathematical repairs.
- Clean project rebuild: `lake clean disjointness`, then `lake --wfail build`.
  Four project modules rebuilt successfully; dependency artifacts were retained.
- Transitive axiom inspection: all seven proved integration results use only
  `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` found.
- Final quota snapshot: 3% used, 97% remaining, same account-wide weekly window.
  The rounded percentage did not change; this does not mean zero resource usage.
- Observed disk use: about 7.5 GiB under the project's `.lake` and 2.8 GiB for the
  Lean toolchain, excluding the separately retained download cache.
- Additional human interventions during setup: none. No additional agents used.

This establishes that PFR reuse is practical at the interface level. It does not
yet estimate the difficulty of the AND analytic proof or coordinate embeddings.

## 2026-10-14 — Phase 2 completed

- Checkpoint: 06:59:22 UTC (02:59:22 America/New_York), about 22 minutes after the
  start of installation/implementation. These times include downloads and builds.
- Continued without a phase-boundary permission request, as agreed.
- Proved tree output decoding, execution-length and leaf-count bounds, transcript
  rectangles, private-seed factorization, and the joint public-seed law identity.
- Constructed a send-input protocol for any Boolean function of Alice's bit vector
  and Bob's input; specialized it to a proved zero-error DISJ protocol of cost `n+1`.
- Proof repairs were local: `simp` had changed a max-bound goal to a disjunction;
  distributivity expanded the two finite sums in opposite orders; an explicit
  function parameter resolved `Finset.le_sup`; `PMF.pure` required a noncomputable
  protocol wrapper. No model assumptions or target claims were weakened.
- Clean build of seven project modules passes with `--wfail`.
- Expanded transitive axiom inspection passes for every public Phase 2 theorem.
- Weekly account snapshot still reports 3% used, 97% remaining. Its granularity
  does not resolve this run's consumption; no per-proof cost claim is justified.
- No additional human intervention or agents used.

Next mathematical obligation: the switch distribution and protocol information
cost, with a proved communication upper bound. No AND/DISJ information lower bound
has been claimed.

## 2026-10-14 — Phase 3 completed

- Start: 07:25:14 UTC (03:25:14 America/New_York), after the user explicitly
  requested Phase 3 and autonomous work to the next milestone.
- Mathematical build and first full axiom audit passed by 07:42:48 UTC, about
  18 minutes after the start. Documentation and clean-build checks followed.
- Defined the switch/input law and proved its exact one-coordinate masses,
  product structure, disjoint support, and conditional independence across players
  and coordinates. Proved the same input law after fixing both `D` and `R`.
- Defined information cost from actual protocol execution. Proved nonnegativity
  and `J ≤ cost * log 2` for every protocol; the general upper bound works for any
  finite input/analysis law and uses no correctness assumption.
- Reused PFR for all entropy reasoning. Added finite PMF joint/product and
  conditioning adapters, joint-law invariance, and a fiberwise support-entropy bound.
- API/proof repairs: explicit finite PMF normalization lemmas; discrete measurable
  structure for `List Bool`; local finite-range instances for finite source spaces;
  exact extended-real inverse arithmetic for the probability sanity check; explicit
  map composition instead of a looping rewrite. These were interface/tactic issues;
  no target or mathematical assumptions were weakened.
- A clean build of all twelve project library modules passes with `--wfail`.
  Every public Phase 3 theorem has a transitive axiom entry, checked against
  `{propext, Classical.choice, Quot.sound}`. No `sorryAx`, project axiom, or
  `native_decide` occurs in the verified development.
- The API docs, LeanArchitect blueprint, and declaration-link check rebuilt
  successfully by 07:46:52 UTC (about 22 minutes total). The new upper-bound and
  conditioning nodes have checked statement/proof markers. The AND/DISJ lower
  bounds remain visibly unproved. The documentation tools emit upstream renderer
  and equational-lemma warnings; these do not occur in the clean Lean proof build.
  Output is retained locally in `docs/explorer-build.log`.
- Account-wide weekly quota snapshots: 4% used at start and 5% at the mathematical
  checkpoint. Concurrent usage is unknown; the rounded difference is not an exact
  per-project or per-lemma cost. Ordinary allowance remains available.
- User-reported setting remains GPT-6 Astra / xhigh. One agent, no additional
  package installation, no dependency upgrades, and no human proof intervention.

Next: Phase 4's Hellinger, cut-and-paste, information comparison, and AND bound.
The model-normalization limitations and unverified candidate constants are unchanged.
## 2026-10-14 — Phases 4–7

- Start: 08:02:30 UTC (04:02:30 America/New_York), after the user requested
  autonomous completion of Phases 4–7.
- The AND proof establishes `1/144` nats using a finite Hellinger/JS layer and an
  exact bridge to PFR conditional information. Correctness at the unsupported
  intersecting input is included; no public seed is assumed individually correct.
- The coordinate decomposition, actual embeddings, private-padding laws, and
  information identity were proved. The finite and reachable-length endpoints
  had compiled by 08:36:08 UTC, about 34 minutes into this run.
- The final extension permits arbitrary probability spaces of random tapes.
  Finite bounded-behavior encoding and measure pushforward give the same error
  law, while truncation removes unreachable deep branches. Measurability and
  the every-tape/every-input length bound remain explicit assumptions.
- Main implementation repairs involved explicit finite-range instances for
  projection functions, dependent `decide` rewrites, explicit functions in PMF
  map-composition rewrites, and non-overlapping recursive encoding equations.
  A direct scalar logarithm/JS proof avoided conversion between the real and
  extended-real KL libraries. No proof goal was replaced with an assumption.
- The library has 25 modules including its root, with 2599 lines in the 24
  mathematical source files (including comments and blank lines). These counts
  describe implementation size, not mathematical complexity or novelty.
- Clean `lake --wfail build` passed. The audit inspected 134 transitive axiom
  lists; every list is contained in `{propext, Classical.choice, Quot.sound}`.
  Source checking found no `sorry`, `admit`, mathematical `axiom`, or
  `native_decide` outside comments. Endpoint types are retained in `axioms.log`.
- No human proof intervention, extra agents, package installation, or dependency
  upgrade was needed during Phases 4–7. The user-reported setting remains
  GPT-6 Astra / xhigh; the environment does not independently attest the active
  model. Final semantic review is by the same agent, not an independent review.
- Weekly account snapshots: 5% used at start, 6% at 08:43:54 UTC. These are rounded
  account-wide observations and do not isolate the project's exact consumption.
  Normal allowance remained available; no credits or resets were purchased or used.

- Final documentation build and declaration-link validation completed by
  08:45:37 UTC (04:45:37 America/New_York), about 43 minutes after this run began.
  All four main lower-bound/normalization nodes are present in the rendered
  blueprint. The documentation renderer's upstream warnings remain separate
  from the warning-free mathematical build.

## Evaluation

The experiment demonstrates autonomous completion of a substantial, known
information-complexity proof in the stated models, including analytic lemmas,
probability interfaces, actual protocol constructions, exact distribution
identities, and normalization. PFR reuse supplied the entropy laws while the
protocol-specific reasoning and finite distance layer were developed locally.

The main reusable pieces are finite PMF conditioning and product replacement,
finite-channel/PFR information adapters, Hellinger/JS inequalities, local
randomized preprocessing, coordinate entropy subadditivity, and bounded-tree
normalization. The final theorem is supported by kernel checking and a transitive
axiom audit; human review should focus on definitions and model correspondence.

This one run does not establish the same reliability or resource requirements
for a larger or novel theorem. It benefited from a known proof route, a detailed
README, pinned libraries, and a working local toolchain. It does not measure
model-to-model differences, independent review quality, or fresh-machine
reproducibility. The next human checkpoint is the exact endpoint and audit,
particularly random-tape measurability and the public-output convention.
