# Decisions

## 2026-10-14 — Initial execution settings

The user delegated routine choices and preferred xhigh. Keep the user-reported
GPT-6 Astra / xhigh setting as the initial baseline; start with one agent. The
environment does not independently attest the active model setting. Report meaningful
milestones and continue routine work. Surface changes to the theorem or resource boundary.

Use the normal weekly allowance only, with about one fifth reserved for integration,
audit, and handoff. Available purchased credits/reset credits do not authorize their use.
Quota observations are account-wide; other account activity is unknown.

## 2026-10-14 — Pin the PFR-compatible dependency set

- PFR: `4c56de547b2f33b0bc47b92f3bfbcebc6457a776`.
- Lean: `leanprover/lean4:v4.35.0-rc4`, as required by that PFR revision.
- Expected mathlib: `a37dcbd570ffe4283df24efc20b144a09cc3661e`, from PFR's manifest.
- The root Lake manifest must record all resolved transitive revisions.

The release candidate is chosen to match the actual entropy library, not as a claim
that a release candidate is generally preferable. Moving web documentation was
observed to disagree with checked-out dependency metadata. Local pinned source is
the authority for implementation.

Import only the needed PFR entropy files rather than its full theorem development.
Our project explicitly enables `warn.sorry`; PFR's package disables that warning.
An axiom inspection of the imported results used here is necessary regardless of warnings.

## 2026-10-14 — Probability representation (integration build passed)

Use mathlib `PMF` on finite types for sampling and `PMF.toMeasure` for PFR's
random-variable entropy API. Finite types carry discrete measurable spaces. Keep
arbitrary real probabilities and natural logarithms. This provides convenient finite
sampling while retaining PFR's existing chain rules and conditional information.

No replacement entropy library is justified yet. Evaluate mathlib's extended-valued
KL API separately from PFR's real-valued finite KL; the latter requires explicit
absolute-continuity assumptions. A finite Jensen–Shannon/Hellinger adapter may be
simpler than a general divergence conversion theorem.

All seven integration lemmas compile and their transitive axiom sets are clean.
Mathlib's KL has type `ℝ≥0∞`; PFR's conditional information has type `ℝ`.
The zero-KL/equal-PMF adapter checks interoperability, but is not yet the
Jensen–Shannon/Hellinger bridge. Some PMF distribution constructors in this pinned
mathlib revision are deprecated in favor of measure constructors. Use `PMF.ofFintype`
or measured-law adapters when needed rather than building on deprecated APIs.

## 2026-10-14 — Protocol representation (definitions compiled)

Use public-seed-indexed finite binary trees with private randomness included in each
player's local argument. Protocol structure enforces locality, public stopping, and
transcript-determined output. Prove rectangle/factorization and support bounds from
the tree; never assume them as model fields. A send-input protocol will test coverage.
Tree-depth cost and finite randomness require the explicit bridges in the blueprint.

The matching definitions and finite-model target now compile in `Protocol.lean`
and `Target.lean`. Model adequacy remains a Phase 2/final-audit obligation. The current
Lean release uses the module system; all project library declarations are explicitly
public, and executable definitions expose their bodies for downstream proofs.

## 2026-10-14 — Phase 2 model check

The chosen tree representation supports a proved zero-error send-input DISJ protocol
of cost `n+1`, a public output decoder, the rectangle property, independent-seed
probability factorization, and the required per-public-seed leaf bound. Keep it for
Phase 3. `Tree.comap` provides proved local input preprocessing, which should support
the later coordinate embeddings without rebuilding protocol semantics.

Factorization is first stated in nonnegative extended-real probability units, matching
PMF's range. Any conversion to real masses for Hellinger must use PMF finiteness.
The public-seed joint law is connected explicitly to the fixed-seed law so that later
correctness comparisons can average over public randomness.
