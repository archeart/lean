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
