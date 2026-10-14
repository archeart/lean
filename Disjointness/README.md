# Disjointness lower bounds in Lean

An experiment in formalizing the information-complexity proof of the randomized communication lower bound for set disjointness, with Codex carrying out most of the work and the human researcher auditing the results.

**Status (2026-10-14): Phases 1–2 complete.** The pinned Lean project builds, seven dependency-integration
results are checked, and the protocol structure, zero-error example, transcript factorization,
and leaf bounds are proved. The DISJ lower bound
is **not proved**. See [current status](docs/status.md), [blueprint](docs/blueprint.md), and
[audit record](docs/audit.md).

## Build and inspect

Install [elan](https://github.com/leanprover/elan#installation), then run from this directory:

```sh
lake exe cache get
lake --wfail build
lake lean Audit.lean
```

The checked-in `lean-toolchain` selects Lean **v4.35.0-rc4**. The Lake configuration pins PFR
at `4c56de547b2f33b0bc47b92f3bfbcebc6457a776`; `lake-manifest.json` pins all transitive
dependencies, including mathlib at `a37dcbd570ffe4283df24efc20b144a09cc3661e`.
The first command downloads dependency sources as needed and mathlib's compiled cache.
The build also compiles the imported PFR entropy modules. No dependency upgrade is needed.

For a clean rebuild of this project's files while retaining dependency caches:

```sh
lake clean disjointness
lake --wfail build
lake lean Audit.lean
```

The clean project rebuild and axiom inspection were run successfully; their outputs are
[clean-build.log](docs/clean-build.log) and [axioms.log](docs/axioms.log). The latest incremental
build is also recorded in [build.log](docs/build.log). A fresh-machine/source-only
reproduction remains part of the final audit. The 3187 reported build jobs include dependency
and cached jobs, not 3187 newly proved project results.

| File | What it currently supplies |
| --- | --- |
| `Disjointness/Integration.lean` | Seven proved entropy/KL integration results |
| `Disjointness/Protocol.lean` | Local binary trees, execution, independent seed laws, pointwise error, tree-depth cost |
| `Disjointness/Tree.lean` | Public decoding, rectangle property, execution-length and leaf-count bounds |
| `Disjointness/Factorization.lean` | Fixed-seed and joint transcript factorization; support/cost bounds |
| `Disjointness/SendInput.lean` | An actual zero-error DISJ protocol of cost `n+1`, including its output bit |
| `Disjointness/Target.lean` | DISJ definition and the named, **unproved** proposition `FiniteLowerBoundClaim` |
| `Audit.lean` | Target printing and transitive axiom inspection |

## Purpose and working arrangement

The immediate mathematical objective is a complete, kernel-checked proof of a linear randomized communication lower bound for two-party set disjointness. The experimental objective is to learn how much mathematical formalization Codex can perform autonomously, what human auditing requires, and which obstacles should inform a larger one-year AI-for-mathematics proposal.

Codex will select and document representations, inspect dependencies, develop the proof blueprint, implement Lean definitions and proofs, run the compiler, repair failures, and maintain the audit record. The human researcher's principal role is to review the statements, decisions, and results. The experiment should not depend on the human supplying detailed Lean proofs or continuously directing tactics.

Routine implementation decisions should proceed autonomously once implementation is authorized. A material change to the target theorem, its assumptions, or the experiment's resource boundary should be surfaced explicitly. Phase boundaries are reporting and audit checkpoints, not automatic requests for permission to continue.

Implementation began after the plan/settings discussion and the user's elan installation.

## Mathematical target

For inputs `x, y : Fin n → Bool`, define `DISJ n x y` to be true exactly when no coordinate is true in both inputs. The intended endpoint is

\[
R^{\mathrm{pub}}_{1/3}(\mathrm{DISJ}_n)=\Omega(n).
\]

The primary Lean theorem should state this directly about protocols, avoiding an unnecessary optimization over all protocols:

> There exist an absolute constant `a > 0` and a threshold `n₀` such that, for every `n ≥ n₀`, every admissible randomized two-party protocol that computes `DISJ n` with error at most `1/3` on every input has worst-case communication cost at least `a * n` bits.

The model must support arbitrary interaction and public randomness, as well as independent private randomness for constructions used inside the proof. Local computation is free. Communication means transmitted bits; random bits are not charged. Cost is worst case, not expected cost. The positive constant need not be optimal.

Start with finite input, random-seed, and transcript types. There must be no imposed bound relating the amount of randomness to the communication cost or input length. Before claiming the conventional public-coin lower bound, audit the model's coverage and prove any necessary normalization bridge. If a bridge remains unproved, the final statement must retain the exact model restriction and the audit must identify it.

Use a convention in which the output is determined by the transcript and public seed. If comparison with another conventional protocol model requires transmitting the output bit, account for that bit explicitly.

## Proof route

Follow the conditional-information argument of Bar-Yossef, Jayram, Kumar, and Sivakumar (BJKS). This experiment concerns their route to the linear communication bound, rather than the later theory of optimal internal information complexity or interactive compression.

For each coordinate, sample a fair switch `Dᵢ`. In one branch set `Xᵢ = 0` and sample `Yᵢ` fairly; in the other set `Yᵢ = 0` and sample `Xᵢ` fairly. Sample coordinates independently. Thus every sampled pair is disjoint, and the input coordinates are independent conditional on the switch vector `D`.

Let `R` denote the protocol's public seed and `T` its communicated transcript. The central quantity is

\[
J(\Pi)=I((X,Y);T\mid D,R).
\]

The switch vector is an auxiliary variable in the analysis, not additional input supplied to the original protocol. With information measured in nats, the intended proof chain is

\[
\operatorname{cost}(\Pi)\log 2
\;\ge\; J(\Pi)
\;\ge\;\sum_{i=1}^{n} I((X_i,Y_i);T\mid D,R)
\;\ge\;\kappa n
\]

for an absolute `κ > 0`.

The last step constructs a valid AND protocol for each coordinate. It publicly samples the switches for the other coordinates, privately samples the corresponding input padding, and runs the original protocol. All padding coordinates are disjoint, so complementing the DISJ output computes AND on the distinguished coordinate. The distinguished switch `Dᵢ` remains an analysis variable, not revealed side information.

The AND lower bound follows from transcript factorization, Hellinger cut-and-paste, an information-to-Hellinger inequality, and separation of transcript distributions forced by correctness. Use an elementary total-variation/Hellinger comparison that remains positive at error `1/3`, rather than relying on a loose estimate that only gives a positive constant at smaller error.

These displayed statements are the intended blueprint. Their precise hypotheses, constants, and Lean interfaces must be checked during implementation.

## Phases and completion criteria

Phases describe dependencies and deliverables, not calendar commitments. Later phases may motivate revisions to earlier interfaces. A phase is complete only when its stated proof obligations are checked; an accepted file containing placeholders does not satisfy a completion criterion.

### Phase 1 — Fix the statement, dependencies, and proof blueprint

**Work**

- Initialize a Lean project and pin the toolchain and dependency revisions.
- Inspect the existing PFR entropy development and mathlib probability/KL APIs. Compile small integration examples before committing to a representation.
- Prefer reuse of existing entropy and conditional-information results. If adaptation is too costly, document the evidence and the scope of any replacement finite-distribution layer.
- Write the precise endpoint and a dependency graph of intermediate claims, including public/private randomness, output conventions, and the nats-to-bits conversion.
- Identify which facts are already available, require adapters, or must be proved here.

**Completion criterion:** a reproducible baseline build, checked dependency-integration examples, and a blueprint whose interfaces expose all substantial assumptions. Unproved target statements remain visibly separate from verified results.

**Audit checkpoint:** what exactly will the final theorem quantify over, and what imported mathematics is being reused?

### Phase 2 — Define protocols and prove their transcript structure

**Work**

- Define finite binary communication trees with Alice and Bob decisions depending only on their own input, their private seed, and available public information.
- Define execution, transcript, output, worst-case communication cost, and pointwise error for randomized protocols.
- Construct and verify a simple send-the-input protocol. This checks that the model expresses ordinary communication protocols and gives a useful cost sanity check.
- Prove the deterministic rectangle property on inputs augmented with private seeds.
- Deduce transcript-probability factorization for each fixed public seed:
  `Pr[T = t | x, y, R = r] = A(r, t, x) * B(r, t, y)`.
- Prove the transcript support bound needed for the entropy upper bound. Use the tree/leaf structure or a verified fixed-length encoding; do not assume that all strings of length at most `c` number at most `2^c`.

**Completion criterion:** checked execution and correctness definitions, a checked example protocol, and proved factorization and transcript-counting results. Rectangle structure and information bounds must be consequences of the model, not fields assumed in its definition.

**Audit checkpoint:** are communication restrictions enforced by the definitions, and are public randomness, private randomness, and output handled correctly?

### Phase 3 — Connect the probability model to information cost

**Work**

- Define the switch/input distribution, including its product and conditional-independence properties.
- Build the finite-distribution/random-variable adapters required by the chosen entropy library.
- Establish the required chain rules, conditional subadditivity, nonnegativity, and invariance under equality in distribution, importing existing theorems where possible.
- Define the protocol quantity `J` and prove `J ≤ cost * log 2`.
- Keep treatment of zero-probability events and logarithm conventions explicit. Public-seed entropy must not be charged as communicated information.

**Completion criterion:** a checked information-cost definition and communication upper bound, with a clear mapping to the paper's notation.

**Audit checkpoint:** are the input law and independence assumptions correct, and does the information cost measure the communicated transcript with the intended conditioning?

### Phase 4 — Prove the information lower bound for AND

**Work**

- Define or reuse Hellinger distance on finite distributions, with an explicit normalization. A convenient squared form is
  `h²(P,Q) = (1/2) * Σ t, (sqrt(P t) - sqrt(Q t))²`.
- Prove the distance inequalities needed by this proof, including the squared triangle estimate and total-variation comparison.
- Prove cut-and-paste from transcript factorization, first for fixed public seed.
- Connect the mutual information of a uniformly chosen binary input to the Hellinger separation of its two transcript laws.
- Use worst-case correctness on all four AND inputs to obtain a positive lower bound for the conditional information cost under the switch distribution.
- Handle public seeds by the appropriate averaging. Correctness of a randomized protocol does not imply correctness for every fixed public seed.
- Record an explicit positive constant once obtained; do not spend effort optimizing it.

**Completion criterion:** a checked AND information lower bound for the same protocol model needed by the coordinate embeddings, at error `1/3`.

**Audit checkpoint:** correctness must include input `(1,1)`, although the information-cost distribution gives that input probability zero. The switch variable must not be exposed to the protocol.

### Phase 5 — Prove coordinate decomposition and construct embeddings

**Work**

- Prove the coordinate information inequality from conditional independence and entropy subadditivity.
- Construct the embedded AND protocols as actual protocols in the formal model, including their public switches, private padding, and original protocol randomness.
- Prove that the constructed inputs have the required joint distribution.
- Prove correctness on every AND input, including the intersecting input outside the information-cost distribution's support.
- Prove the identity relating each embedded protocol's information cost to its corresponding coordinate term.
- Apply Phase 4 and sum over coordinates.

**Completion criterion:** a checked theorem `κ * n ≤ J(Π)` for every admissible protocol computing DISJ with the required error.

**Audit checkpoint:** are the embeddings implementable using only allowed information, and are distribution identities proved rather than assumed?

### Phase 6 — Assemble the communication lower bound

**Work**

- Combine the upper and lower bounds on `J` and convert nats to communicated bits.
- Resolve small dimensions, positivity of constants, output-convention overhead, and any required protocol-model normalization.
- State the final theorem with its constants and quantifier order explicit.
- Optionally package the result in asymptotic or communication-complexity notation after the direct protocol theorem is proved.

**Completion criterion:** the complete lower bound builds with no unproved project assumptions in its dependency chain. Any outstanding model extension is named as a limitation rather than silently included in the claim.

**Audit checkpoint:** does the Lean theorem establish the advertised randomized, interactive, public-coin result, with worst-case error and worst-case communication?

### Phase 7 — Audit, reproduce, and evaluate the experiment

**Work**

- Perform a separate review of the endpoint and definitions against the mathematical statement. Check for vacuous protocol classes, accidentally strengthened assumptions, restricted correctness, or conclusions hidden in hypotheses.
- Inspect the endpoint's transitive axioms, using `#print axioms` and source review. Ordinary Lean/mathlib foundations such as `propext`, `Classical.choice`, and `Quot.sound` are acceptable; `sorryAx` and unproved mathematical project axioms are not.
- Reproduce the build from pinned dependencies and document the actual commands and results.
- Produce a paper-to-Lean correspondence identifying the files and declarations for each major proof step.
- Summarize resource use, human interventions, failed approaches, reusable infrastructure, and remaining limitations.
- Assess what the experiment supports about a larger project, distinguishing measured results from extrapolation.

**Completion criterion:** a reproducible theorem package and an audit report that lets the human researcher inspect what was proved, how, and at what cost.

## Scope boundaries

The first implementation should use the simplest adequate representations for this proof. General-purpose framework design is justified only when it removes a concrete obstacle or supports a near-term proof obligation.

The following are outside the initial experiment: the corruption proof, optimal constants, expected-communication bounds, quantum or multiparty protocols, general interactive compression, and a broad library of information-complexity minimization theorems. The corruption route remains a possible later comparison using shared infrastructure.

## Progress and audit records

Supporting records:

| Record | Purpose |
| --- | --- |
| `docs/blueprint.md` | Precise intermediate statements, dependencies, and correspondence with the paper |
| `docs/status.md` | Current checked results, open obligations, blockers, and next action |
| `docs/decisions.md` | Significant representation choices, alternatives tested, and reasons for changes |
| `docs/experiment-log.md` | Resource observations, human interventions, and failed or successful approaches |
| `docs/audit.md` | Statement review, axiom inspection, reproduction results, and known limitations |

These files now exist. Keep records concise and update them at meaningful milestones rather than after every tactic edit.

Each milestone report should state what now compiles, what mathematical claim it establishes, what remains unproved, and which decisions affect the human audit. Distinguish a fully proved theorem, a theorem conditional on named hypotheses, and a target statement awaiting proof.

## Resource discipline and stopping conditions

The initial evaluation budget is one normal weekly Codex allowance, subject to the user's eventual execution instructions. This is a resource boundary, not a promise to finish all phases within a week. This README does not authorize purchasing credits, applying account resets, or continuing beyond the agreed boundary.

Record quota snapshots where available, with model/settings and concurrent account usage when known. Account-wide percentages are coarse observations, not exact per-lemma costs. Record wall-clock time and human interventions separately; neither can be inferred reliably from quota consumption.

Use early completed proof obligations to recalibrate scope. Reserve approximately one fifth of the agreed resource budget for integration, audit, and a usable handoff. If repeated attempts stop producing new evidence, revisit the lemma statement, representation, or library interface and document the decision.

If the budget is reached before the endpoint, finish with a building verified subset, explicit unresolved obligations, and a revised estimate. A partial result is useful experimental evidence; it must not be reported as a complete DISJ formalization.

## What counts as success

- **Mathematical completion:** the full endpoint and its supporting proof chain are checked and audited.
- **Useful partial mathematical result:** a substantial component, such as the AND information lower bound or the coordinate embedding theorem, is checked with its exact remaining assumptions visible.
- **Experimental result:** the record identifies which parts Codex completed autonomously, which required human intervention, what infrastructure was missing, and what should change in a subsequent attempt.

Generated code volume, raw theorem counts, or a compiling file with the central result assumed do not measure completion.

## References and candidate dependencies

- Z. Bar-Yossef, T. S. Jayram, R. Kumar, and D. Sivakumar, *An information statistics approach to data stream and communication complexity*, JCSS 68 (2004), 702–732. [Paper PDF](https://people.seas.harvard.edu/~madhusudan/courses/Spring2016/papers/BJKS.pdf). Sections 4–6 provide the principal route; relevant statistical inequalities appear in the appendices.
- [PFR entropy documentation](https://teorth.github.io/pfr/docs/PFR/ForMathlib/Entropy/Basic.html) and [PFR repository](https://github.com/teorth/pfr). Candidate source of Shannon entropy, conditional entropy, mutual information, and conditional-information identities.
- [mathlib KL-divergence documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/InformationTheory/KullbackLeibler/Basic.html) and [mathlib repository](https://github.com/leanprover-community/mathlib4). Candidate source of probability and analytic foundations.

Build compatibility and the initial entropy interfaces were checked in Phase 1. Revisions actually
used are pinned in the project; the documentation links above may describe different revisions.
