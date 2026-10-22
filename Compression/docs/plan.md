# BBCR Theorem 2.2: proof plan

Theorem 2.2 is complete in the finite model. The active next target is Theorem
2.1. Its internal-information accounting, finite threshold sampling, square-root
mistake estimate, zero-message small-information branch, and the separate search
analysis/compiler components are checked. The remaining construction connects
the compiled search to its error law, implements the capped local correction
loop, and combines its errors and communication budget. The precise boundary
between checked results and the open endpoint is recorded in `status.md`.

Source: Barak, Braverman, Chen, Rao, *How to Compress Interactive Communication*,
SIAM J. Comput. 42(3), 2013, pp. 1327–1363; `../../papers/BBCR.pdf`.
The endpoint is Theorem 2.2, not the direct-sum application Theorem 2.6.

## Precise endpoint

For every finite input distribution μ and finite-seed private/public-coin binary
protocol π of worst-case communication C, construct a binary protocol τ and two
local decoders into the original public-seed/transcript alphabet. Require:

1. The μ-average of the conditional total-variation distances between Alice's
   decoded transcript law and the original transcript law is at most α.
2. The μ-average probability that the two decoders disagree is at most α.
3. The worst-case communication is at most
   `K * I_ext(π, μ) * log((C + 1) / α) / α²`, for one absolute K > 0.

Use `0 < α ≤ 1/2`. Information and logarithms are in nats; the absolute constant
absorbs conversion to bits. `C + 1` makes the logarithm meaningful at C = 0 and
is equivalent up to a constant factor to the paper's bound for C ≥ 1.
The error guarantee is stronger than comparison of unconditional transcript
marginals: it retains the input/transcript correlation needed by applications.
This endpoint is now proved by `BBCR.theorem_2_2` and the uniform
`BBCR.externalCompressionClaim` in `Theorem22.lean` (2026-10-17).

## Dependencies and milestones

1. **Protocol and simulation interfaces.** Reuse binary execution, finite views,
   locality, factorization, PMFs, and PFR entropy. Define external information,
   input-conditional fidelity, local-decoder agreement, and the uniform claim.
   Check the identity simulator and the information/communication bound.
2. **Finite divergence accounting (8.1–8.2).** Define supported finite KL with
   explicit absolute-continuity hypotheses. Connect averaged conditional KL
   to PFR mutual information; prove the conditional chain-rule accounting.
   Zero-probability fibers must not contribute spurious terms.
3. **Rejection sampling (Appendix B; 8.5).** Construct accepted-sample laws,
   prove their normalization, acceptance probabilities, and clipping bounds.
   Then connect these laws to a bounded, implementable two-party sampler.
4. **Smoothing (Lemma 8.4).** Replace each intended bit by biased independent
   bits; use majority decoding and concentration. Prove a coupling to π,
   smoothness, communication inflation, and the good-run divergence tail.
   Success conditioning must be justified using symmetry of the noise.
5. **Smooth compression (Theorem 8.5).** Define divergence stopping frontiers;
   prove exact frontier factorization (8.5), likelihood-ratio concentration
   (Claim 8.9), clipped-sampling distortion (8.7), and expected cost (8.8).
   Assemble rounds and truncate with explicit error and worst-case cost.
6. **Theorem 2.2.** Compose smoothing and compression, choose explicit constants,
   audit small/zero-information cases, inspect axioms, and reproduce the build.

## Reuse boundaries

The DISJ, AND, and BJKS lower-bound theorems are not mathematical prerequisites.
The current local dependency supplies the infrastructure without changing the old
development. Some reusable modules still transitively contain specialized BJKS
definitions; extraction into a shared package can wait until interfaces stabilize.

The existing arbitrary-tape reduction makes deterministic behavior public. It is
not an information-preserving normalization and must not be used to justify the
compression endpoint. Initially retain finite public/private seed types with
arbitrary real probabilities and no seed-cardinality bound. An arbitrary-tape
extension would need its own information-preserving proof.

The Section 8 concentration argument is the main new mathematical obstacle.
A finite branching-process Azuma theorem with a pathwise squared-width budget
has now been checked in `FiniteAzuma.lean`. Its instantiation with the stopped
log-likelihood process and its energy budget are now checked in
`StoppedAzuma.lean`, `FrontierBudget.lean`, and `FrontierLikelihood.lean`. Prefix
locality, the conditional interval accounting of Lemma 8.2, its full external-
information identity, and the smoothing communication and fidelity construction
have also been checked. The constructed protocol's beta-smoothness, its observer
kernel bounds, and the actual local divergence bound in Proposition 8.6 are now
checked. The good-event information comparison and an information-inflation
variant of the original-information tail estimate are also checked. Explicit
parameters now absorb the correction, keep communication inflation within a
cubic logarithm, and meet the smoothness condition using the smoothed cost.
The exact formulation of Lemma 8.4 is not asserted; see `status.md` for the boundary.

## Checked: good-event information comparison for smoothing

Section 4.2 and Figure 4 of BBCR present protocols by fresh sampling from local
node kernels. Our model also permits a persistent private seed, and the current
transformation retains it. Before using the paper's intended-message good-run
identities verbatim, an information-preserving normalization to that node-kernel
presentation would need a proof. The existing public-random-tape reduction does
not supply it.

The implementation uses the independent event that both entire noise tapes are
good. The following steps are now checked:

1. On this event the full physical smoothed transcript is a function
   of the original public transcript and the noise tapes. The checked public
   decoder proves recovery in the other direction; `run_encodedTrace_of_good`
   proves the forward factorization without examining inputs or original seeds.
2. Conditioning on the good-noise event leaves the original experiment's law
   unchanged and preserves its independence from the noise. Data processing
   bounds conditional good-run information by the original information,
   separately for each public seed. Null good events have zero information.
3. The input-independent-flag averaging inequality and a bad-run communication
   bound give `externalInformation_le_original_add_bad`:
   `I_ext(smoothed) ≤ I_ext(original) + δ m C log 2`, where `δ` is the probability
   that either player's whole noise tape is bad. The iid bound is
   `δ ≤ 2 (C+1) exp(-2 m β²)`. `smoothing_divergence_tail_le` combines this
   protocol-level comparison with the actual accumulated-divergence Markov bound.

## Checked: smoothing parameters and communication logarithms

For `0 < α ≤ 1` and `0 < β ≤ 1/2`, choose

```text
m = ceil_nat(log(2 (C+1)² / (α² β²)) / β²) + 1.
```

`SmoothingParameters.lean` verifies fidelity error at most `α`, information
increase at most `α²`, and
`m ≤ (3 log((C+1)/(α β)) + 2) / β²`. The checked
`small_information_compression` handles `I_ext ≤ α²` with zero communication.
In the remaining regime the same concrete smoothed simulator has information
at most `2 I_ext` and `Pr[D_smoothed ≥ 2 I_ext / α] ≤ α`.

For the endpoint range `0 < α ≤ 1/2`, let `L = log((C+1)/α)` and choose
`β = 1/(4 k L)` with `k ≥ 1`. `SmoothingScale.lean` proves `m ≤ 544 k³ L³`,
so the actual communication `C'` is at most `544 k³ L³ C`.
`SmoothingLogBudget.lean` checks the self-consistency needed by Theorem 8.5:
for any prospective constant `κ ≥ 1`, choose `k = (32 κ)²`. The concrete
simulator satisfies

```text
Smooth(protocol, 1 / (κ log((C'+1)/α))),
log((C'+1)/α) ≤ 1476 κ L.
```

Thus stronger noise accuracy introduces no extra logarithmic order into the
final information-dependent budget. These are preprocessing theorems for every
`κ ≥ 1`; no smooth compressor or compressor-cost hypothesis is assumed.

## Checked: divergence frontiers and equation (8.5)

`StoppingFrontier.lean` constructs finite first-hit frontiers, normalized
sampling laws, and an exact finite-alphabet representation. The endpoints form
an antichain, every complete continuation meets exactly one endpoint, and the
stopping test is false at each strict ancestor. A common stopping rule preserves
pointwise edge factorization for four kernel families.

`StoppedExecution.lean` identifies the sampler with the original experiment
conditioned on a positive starting prefix and stopped at the first hit. The
proof uses actual unnormalized transition identities and handles null branches;
it does not assume fresh private seeds after conditioning.

`ProtocolFrontier.lean` instantiates stopping when either player's accumulated
local KL reaches the threshold or a public leaf is reached. Its observer and
target laws equal stopped conditional executions. Alice's hybrid law uses her
local kernel at Alice nodes and the observer kernel elsewhere; Bob's is the
analogous law. Their edge identity gives the cross-multiplied equation (8.5)
for the actual frontier laws, without a factorization hypothesis.

`FrontierRejection.lean` places all four laws on the same finite alphabet and
proves positive observer mass from strict smoothness at a positive starting
prefix. The acceptance-rate and accepted-law distortion estimates are now
instantiated for the concrete frontier. The explicit bad-mass hypothesis in
this algebraic layer is now discharged by `FrontierLikelihood.lean` and `FrontierSampling.lean`.

## Checked: concentration and an actual frontier trial

The stopped local log-likelihood process has conditional mean equal to local
KL, squared range at most `64 KL`, drift at most `9β`, and squared-width sum at
most `576β`. The resulting Claim 8.9 bound is explicit. At clipping level
`exp 1`, a reciprocal-log smoothness parameter gives error
`2 (α/(C+1))⁴ ≤ 1/8`, constant acceptance rate, and both TV and pointwise
control of the accepted frontier law.

`FrontierLocation.lean`, `LocalRejection.lean`, and `IndexedRejection.lean`
implement the messages using actual binary trees and finite private random
tables. `FrontierTrial.lean` instantiates them for the protocol frontier. The
public proposal is independent of the actual input pair; the cutoff is located
through the two local indices. Its public decoded law is exactly the clipped
rejection trial, and its bit cost is at most `2 ceil(log₂(C+1)) + 2`.

## Completed: exact likelihood frontiers and amortized index cost

The final construction replaces the divergence threshold by first exit of either
player's accumulated log likelihood from `(-1,1)`, or a public leaf. For
`ε ≤ 1/8`, the crossing increment is at most one, so both stopped log ratios
lie in `[-2,2]`. Rejection with clipping level `exp 2` therefore clips nothing:
its acceptance rate is the constant `ρ = 1/(exp 2)²`, and its accepted law is
exactly the target frontier.

`LikelihoodCharge.lean` uses `exp(-z)-1+z` to prove that target probability of a
nonterminal frontier is at most four times its KL divergence. The divergence
equals the drop in residual expected information (`LikelihoodAccounting.lean`).
`ResidualInformation.lean` identifies the average initial residual with the
original external information exactly.

The lazy index protocol sends two flags and two acceptance bits on every trial;
it sends binary indices only when either local cutoff precedes the common
public leaf index. Candidate probability of this event is controlled by the
target probability through the bounded likelihood ratios. Expected index cost
is thus charged to residual information with coefficient
`8 exp(4) width(C) / ρ`, with no reciprocal smoothness factor.

`FiniteDynamics.lean` checks the potential budget and a completion bound using a
centered success count and finite Azuma. `ProtocolIteration.lean` compiles the
process into actual trees with fresh independent finite seed tables, a public
state decoder, and bit truncation. The compiled seed law equals the analyzed
finite dynamics. `LikelihoodCompletion.lean` proves preservation of every
terminal payoff and the original continuation law. Consequently unfinished
execution bounds fidelity error.

For smooth compression at error α, the explicit parameters are

```text
N = ceil_nat(32 I/(ρ α) + 8 log(4/α)/ρ²) + 1,
A = 8 exp(4) width(C) / ρ,
Q = 4 N + ceil_nat(4 A I/α) + 1.
```

`LikelihoodSimulation.lean` proves bounded-tree fidelity, and
`LikelihoodSimulator.lean` mixes over the original public seed without
publicizing private randomness. `LikelihoodBounds.lean` averages the residual
potential to external information. `CompressionParameters.lean` checks the error
allocation. In the regime `α² ≤ I`, `CompressionCost.lean` proves
`Q ≤ K₀ I log((C+1)/α)/α²` with an explicit positive constant. The complementary
regime uses the checked zero-communication public sampler.

`SmoothCompression.lean` proves the actual smooth-compression theorem.
`SimulatorComposition.lean` checks public-decoder composition.
`Theorem22.lean` applies smoothing and compression at error `α/2`, bounds the
smoothed information by `2 I`, and transfers its communication logarithm to the
original one. One admissible final constant is `400000 K₀`. This proves the
original finite-model `ExternalCompressionClaim` without a compressor
hypothesis.

The proof retains the previously checked information-inflation smoothing
variant; it does not assert the paper's exact intermediate Lemma 8.4. All
obligations for the stated finite-model endpoint are discharged. Extensions to
infinite random-tape spaces are outside this endpoint.

## Validation

Run `lake --wfail build` and `lake lean Audit.lean` from `Compression/`.
No `sorry`, unproved mathematical axioms, or hypotheses assuming the compressor
may enter a theorem advertised as Theorem 2.2. Audit the dependency axioms and
distinguish algebraic sampling laws from an actual communication protocol.
