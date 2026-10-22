# Interactive compression in Lean

**BBCR Theorem 2.2 is proved in the finite protocol model.**
The endpoint is `BBCR.theorem_2_2`, and `BBCR.externalCompressionClaim` proves
the uniform statement originally recorded in `Simulation.lean`.

**Theorem 2.1 is in progress; its uniform endpoint is not proved.** The checked
components include the standard internal-information identity, exact public
threshold sampling of the original transcript, the expected mistake bound
`E[M] ≤ sqrt(C * I_int)`, its Markov tail, and an actual zero-message simulator
when `C * I_int ≤ ε²`. Zero internal information has an exact zero-message
simulator, including for correlated inputs. The first-difference search has
checked finite fingerprints, backtracking concentration, binary search-step
protocols, and an adaptive communication-tree compiler. Connecting that compiler
to the concentration estimate and implementing the capped correction loop
remain open; see `docs/status.md`.

For every finite input prior μ, finite public/private seed spaces, binary
protocol π, and `0 < α ≤ 1/2`, the theorem constructs an actual local binary
protocol with decoders into π's original public-seed/transcript alphabet.
It proves:

- μ-average total variation of the input-conditional decoded law is at most α;
- μ-average disagreement probability is at most α;
- worst-case communication is at most
  `K * I_ext(π, μ) * log((C + 1) / α) / α²` for one explicit absolute `K > 0`.

Information is measured in nats and communication in bits. `C+1` covers zero
communication. The finite input and seed assumptions and the error range are
explicit in the theorem. This project does not extend the endpoint to arbitrary
measurable infinite random-tape spaces.

The final proof uses constant log-likelihood stopping frontiers. Their accepted
law is exact, with constant acceptance probability. The protocol sends index
encodings only when a proposal stops before a public leaf. Their expected cost
is charged to the drop in remaining information. This avoids the additional
logarithm in the earlier divergence-frontier accounting attempt.

`ProtocolIteration.lean` compiles the adaptive loop into communication trees
with independent finite private random tables and a public state decoder.
`LikelihoodSimulation.lean` proves fidelity after a fixed bit cutoff.
`LikelihoodSimulator.lean` mixes over the original public seed.
`CompressionParameters.lean` and `CompressionCost.lean` supply explicit trial
counts, cutoffs, and the single-log cost estimate. `Theorem22.lean` composes this
with the checked noisy-block smoothing transformation and handles small
information by public sampling with zero communication.

The smoothing proof controls information by an explicit good-event comparison.
It is an information-inflation variant of the paper's intermediate smoothing
estimate; the final theorem retains the original target budget. Earlier checked
components include finite-model Lemma 8.2, the divergence frontiers, Claim 8.9,
and clipped two-party rejection sampling.

The sibling `Disjointness` package supplies protocol trees, finite views,
probability tools, and information infrastructure. The compression theorem does
not use a disjointness lower-bound theorem. Retain that sibling directory when
reproducing this monorepo-local package.

Validation uses Lean `v4.35.0-rc4` and the pinned shared dependencies:

```sh
lake --wfail build
lake lean Audit.lean
```

Both commands pass. `docs/build.log` and `docs/axioms.log` record the checks.
The endpoint depends only on `propext`, `Classical.choice`, and `Quot.sound`;
there are no admitted proofs or added mathematical axioms.

See [the proof plan](docs/plan.md) and [the detailed status](docs/status.md).
The supplied paper is `../papers/BBCR.pdf`.
