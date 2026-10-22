# Status

Updated 2026-10-17. **Theorem 2.2 is proved for the stated finite protocol model.**

## Theorem 2.1: checked components and open endpoint

The full Theorem 2.1 is **not proved**. `InternalCompressionClaim` records the
target `K * sqrt(C * I_int) * log((C+1)/ε) / ε`; it is not used as an assumption.

- `InternalInformationBridge.lean` identifies internal information with
  `I(X;T | Y) + I(Y;T | X)` under the original joint execution law.
- `InternalAccounting.lean` identifies the expectation of the two
  receiver-conditioned path KL sums with `internalInformation`.
- `ThresholdCoupling.lean` constructs finite threshold tables with exact
  Bernoulli marginals and disagreement equal to binary total variation.
- `InternalPredictions.lean` and `InternalMistakes.lean` prove the local squared
  disagreement charge and the bound `expectedDisagreement ≤ sqrt(C * I_int)`.
- `InternalSampling.lean` proves that following each speaker's table entry
  produces the original transcript law, including persistent private coins.
- `InternalSamplingCost.lean` proves the actual table's expected mistake bound
  and its Markov truncation estimate.
- `SmallInternalInformation.lean` constructs an actual zero-message simulator
  with both errors at most `sqrt(C * I_int)`. The endpoints are
  `small_internal_information_compression` and
  `zero_internal_information_compression`.
- `FiniteHashing.lean` and `FingerprintProtocol.lean` prove exact finite
  fingerprint collision laws and an actual five-bit equality test.
- `FirstDifferenceGeometry.lean`, `NoisySearchDrift.lean`, `NoisyTreeWalk.lean`,
  `BalancedSearch.lean`, and `FirstDifferencePrefixes.lean` prove the robust
  backtracking score estimate, interval geometry, and sentinel handling.
- `FirstDifferenceOracle.lean` discharges the walk's comparison-error premises
  using finite fingerprints. The analyzed process returns a wrong index with
  probability at most `exp(-n/128)` when `n ≥ 4t`.
- `FirstDifferenceStep.lean` implements each search step with 22 actual bits.
  `FirstDifferenceSearch.lean` compiles adaptive steps, bounds communication by
  `22n`, and proves that the public decoder reconstructs the executed state.
- `CorrectionRecursion.lean` proves deterministic correctness whenever the
  correction cap covers the true path's mistake count. This recursion specifies
  free advancement through equal local predictions; its implementation via
  first-difference searches is still open.

The remaining obligations are substantive:

1. Identify the compiled search's seed law and dynamics with the analyzed walk,
   and choose `n = O(log(C/β))` for search error `β`.
2. Compile the capped transcript-correction loop, with locally decoded prefixes,
   and prove that every successful correction consumes a threshold mistake.
3. Combine the Markov tail and adaptive search-error union bound, allocate the
   errors, and prove the uniform single-log communication bound.

No assumed first-difference compressor, admitted proof, or new mathematical
axiom replaces these remaining obligations.

## Completed Theorem 2.2 endpoint

`BBCR.theorem_2_2` constructs the simulator and proves the required error and
worst-case communication bounds. `BBCR.externalCompressionClaim` proves the
uniform endpoint, with one explicit positive absolute constant. The hypotheses
are finite inputs and public/private seed spaces and `0 < α ≤ 1/2`.

## Checked mathematical components

| Component | File and principal declarations | Paper correspondence |
| --- | --- | --- |
| Real finite KL with explicit support, nonnegativity, and its exact PFR mutual-information identity | `FiniteInformation.lean`: `divergence_nonneg`, `information_eq_average_divergence` | Proposition 4.9; part of Lemma 8.2 |
| Conditional channel identity and finite transcript chain rule | `InformationChain.lean`: `conditionalInformation_eq_condMutualInfo`, `conditionalInformation_eq_average_divergence`, `information_vector_chain` | Generic information identities needed for Lemma 8.2 |
| Actual prefix rectangles and private-seed factorization | `ProtocolPrefix.lean`: `Tree.run_prefix_iff`, `Protocol.law_factorization`, sender/non-sender factor identities | Prefix form of the protocol rectangle structure |
| Actual conditional message laws with sender locality | `PrefixKernels.lean`: `next_eq_alice`, `next_eq_bob`, `weighted_mass_next`; `PrefixExperiment.lean`: `next_eq_conditional_message` | The local kernels used in Definition 8.1, tied to execution rather than postulated |
| Finite conditional laws and their measure-theoretic bridge, including null-fiber weighted identities | `FiniteCondition.lean`: `weighted_mass_law`, `weighted_pair`, `toMeasure_law_of_pos` | Makes the actual execution/PFR connection precise |
| One-step local KL accounting for arbitrary correlated priors | `PrefixInformation.lean`: `conditioned_input_message`, `step_divergence_eq_information` | Reached-prefix, one-step form of Lemma 8.2 |
| Variable-length transcript chain rules, also after conditioning on a prefix | `TranscriptChain.lean`: `information_take_chain`, `information_interval_given_prefix`; `PrefixInformation.lean`: `interval_information_actual` | Exact interval chain-rule part of Lemma 8.2, with optional next bits to record stopping |
| Public stopping rule, padded-bit chain rule, and accumulated actual divergence | `PrefixStructure.lean`: `speaker_take_eq_none_iff`, `information_history_chain`; `PrefixAccounting.lean`: `expected_path_divergence`, `expected_full_divergence` | Actual message-by-message accumulation, with zero divergence after termination |
| Refinement of conditional histories and the conditional interval identity, including null initial prefixes | `FiniteCondition.lean`: `sum_fibers`, `law_refinement`; `ConditionalAccounting.lean`: `conditional_interval_divergence_measure` | Finite-model version of Lemma 8.2, proved with equality |
| General disintegration over analysis/public seeds and the full external-information identity | `PublicInformation.lean`: `informationCost_eq_public_average`, `expected_divergence_eq_externalInformation` | Connects accumulated divergence to the actual external-information definition for arbitrary priors |
| Nonnegativity on actual execution support and the basic divergence tail bound `Pr[D ≥ t] ≤ I_ext/t` | `PrefixAccounting.lean`: `pathDivergence_nonneg`; `DivergenceTail.lean`: `divergence_tail_le` | Markov consequence of Lemma 8.2; this alone is not the smoothing comparison in Lemma 8.4 |
| Explicit smooth-step bound `D(p || q) ≤ 8β` for `0 ≤ β ≤ 1/4` and the stated atom bounds | `FiniteInformation.lean`: `smooth_divergence_le` | Proposition 8.6 |
| Normalized rejection law, clipping domination, and total-variation control | `Rejection.lean`: `rate_ge_of_exception`, `accepted_le_target`, `accepted_close` | Algebra underlying Appendix B.2–B.3 |
| Capped retries with exact failure `(1-rate)^n` and success-output law | `BoundedRejection.lean`: `mass_bounded_none`, `mass_bounded_some` | Bounded implementation of the sampling law; not yet a communication protocol |
| Two local clipped acceptance weights: rate at least `(1-δ)/t²` and accepted law within δ of target | `TwoPartyRejection.lean`: `rate_lower`, `accepted_close` | Algebraic parts of Claims 8.7–8.8, conditional on the explicit finite-law factorization and bad-mass hypotheses |
| Normalized first-hit sampling laws, antichain endpoints, unique intersection, strict-ancestor stopping tests, and exact finite-alphabet conversion | `StoppingFrontier.lean`: `paths_antichain`, `unique_frontier_prefix`, `not_halt_take`, `weighted_mass_law`, `law_factorization`, `finiteLaw_map_val` | Finite stopping-tree structure for the divergence frontier in Section 8.3 |
| Recursively sampled frontier law equals actual stopped conditional execution at a positive starting prefix, with null branches handled | `StoppedExecution.lean`: `weighted_stopped_mass`, `law_eq_stoppedExecution` | Connects the sampling analysis to persistent original private seeds |
| Concrete divergence cutoff, strict interior budgets, four normalized frontier laws, actual target/observer execution identities, and equation (8.5) | `ProtocolFrontier.lean`: `accumulated_lt_before_frontier`, `hit_terminal_condition`, `targetLaw_eq_execution`, `observerLaw_eq_execution`, `law_factorization` | Input-dependent frontier and its likelihood factorization, proved from sender-local kernels |
| Finite frontier factorization and positive observer atoms from strict smoothness; concrete acceptance-rate and conditional distortion bounds | `FrontierRejection.lean`: `finite_factorization`, `observer_positive`, `rejection_rate_lower`, `rejection_accepted_close` | Algebraic layer; later concentration modules discharge its bad-mass hypothesis |
| Smooth binary log-likelihood squared range at most `64 KL` | `LogLikelihood.lean`: `logIncrement_width_sq` | Explicit local analytic bound used in Claim 8.9 |
| Stopped execution realized as a centered finite Azuma process with exact law, drift, and energy identities | `StoppedAzuma.lean`: `process_law`, `process_centered`, `process_energy`, `increment_tail` | Instantiation machinery for the path-dependent Azuma bound |
| Positive input/observer reach propagates along all active branches; each stopped player drift at most `β + 8ε` | `FrontierBudget.lean`: `reached_child`, `local_divergence_mem`, `stopped_divergence_budget` | Support and final-overshoot budget needed for concentration |
| Actual frontier log-ratio tail and exponentially small clipped mass with explicit constants | `StoppedLikelihood.lean`; `FrontierLikelihood.lean`: `player_logRatio_tail`, `badMass_le`, `badMass_exp_one` | Claim 8.9 checked for both players |
| Polynomial clipping error, constant positive acceptance, accepted TV error and pointwise domination | `FrontierSampling.lean`: `badMass_polynomial`, `accepted_frontier_bounds`; `TwoPartyRejection.lean`: `accepted_mass_le` | Quantitative sampling estimates underlying Claims 8.7–8.8 |
| Local cutoff indices have the common frontier as their minimum; actual binary exchange with exact execution and depth bound | `FrontierLocation.lean`: `halt_local`, `frontier_index_min`, `exchange_run`, `exchange_depth` | The index communication in Figure 9, explicitly charged |
| Actual private finite-table acceptance coins, two-bit trial, and exact rejection output law | `LocalRejection.lean`: `protocol`, `decoded_law` | Implements the local accept/reject messages without assuming continuous random seeds |
| Actual indexed trial with local index exchange, independent private acceptance, public decoder, and exact law | `IndexedRejection.lean`: `decoded_law`, `cost_le` | Generic implementable proposal/acceptance trial |
| Input-independent public path gives exact observer frontier law; concrete trial implements clipped frontier rejection with explicit communication | `FrontierTrial.lean`: `candidateLaw_frontier`, `trial_acceptance`, `trial_decoded_law`, `trial_cost_le` | One actual trial of Figure 9, not the whole compressed simulation |
| Finite Hoeffding MGF estimate via mathlib | `Concentration.lean`: `finite_hoeffding` | Lemma A.2 |
| Azuma with history-dependent conditional ranges and a pathwise squared-width budget | `FiniteAzuma.lean`: `Process.compensated_mgf_le`, `Process.azuma` | Finite branching-process, centered-increment version of Theorem A.1 |
| Independent biased-noise block with majority error at most `exp(-2 n β²)` | `SmoothingNoise.lean`: `majority_error_le` | Noise estimate used in Lemma 8.4; not the whole lemma |
| Actual noisy-block tree transformation, public decoder, and pointwise recovery on good tapes | `TreeBlocks.lean`; `SmoothingTree.lean`: `smooth_depth_le`, `decode_run_of_good`, `smooth_output_of_good` | Structural part of the smoothing construction in Lemma 8.4 |
| Finite coupling estimate and actual randomized smoothing simulator | `FiniteCoupling.lean`: `variation_map_le_disagreement`; `SmoothingProtocol.lean`: `cost_le`, `fidelity_le`, `simulates` | Couples decoded full transcripts while keeping the original public/private seed marginals |
| Iid tape failure bound, uniform transcript fidelity, and explicit block-size choice | `SmoothingCoupling.lean`: `bad_tape_le`, `smoothing_simulation`, `smoothing_at_error` | Cost/fidelity part of Lemma 8.4 |
| Product-noise identity, actual single-coordinate resampling, prefix causality, and next-message toggling | `NoiseResampling.lean`: `iid_law`, `tapeLaw_resample`; `NoiseCausality.lean`: `fresh_prefix`; `NoiseNextBit.lean`: `fresh_message_complement` | Freshness established from execution, including after conditioning on a physical history |
| Conditional fresh-coin bound and beta-smoothness of the same actual simulator | `FreshCoin.lean`: `fresh_coin_conditional`; `SmoothingSmoothness.lean`: `SmoothingProtocol.smooth`, `smooth_simulation` | Definition 8.3 and the smoothness part of Lemma 8.4 |
| Observer-kernel bounds and actual reached divergence in `[0, 8 β]` for `β ≤ 1/4` | `SmoothDivergence.lean`: `observerNext_mass_mem`, `reached_divergence_mem` | Proposition 8.6 instantiated for actual protocol kernels and execution support |
| Independent randomization, noise-event conditioning, independent-flag averaging, and support-cardinality information bounds | `NoisyInformation.lean`: `independent_randomization_information_le`, `noise_conditioned_information_le`, `information_le_flag_average`, `information_le_of_support` | Generic information tools for (8.3) and the smoothing comparison, including null conditional measures |
| Full physical transcript factors through the original transcript and good noise; actual execution separates into the original experiment and independent tapes | `SmoothingTree.lean`: `run_encodedTrace_of_good`; `SmoothingInformation.lean`: `execution_regroup`, `noisyTranscript_of_good` | Structural and independence justification for the whole-tape good-event argument, also with persistent private seeds |
| Conditional good information at most original information; bad information at most `m C log 2`; total external information at most `I_ext(original) + δ m C log 2` | `SmoothingInformation.lean`: `good_event_information_le`, `bad_event_information_le`, `externalInformation_le_original_add_bad` | Checked information-inflation variant of the smoothing comparison; not the paper's exact Lemma 8.4 |
| Iid correction `δ ≤ 2 (C+1) exp(-2 m β²)`, original-information divergence tail, and all four smoothing guarantees for the same simulator | `SmoothingTail.lean`: `bad_noise_le`, `smoothing_information_le`, `smoothing_divergence_tail_le`, `smoothing_with_information` | Quantitative smoothing information/tail estimates before the final parameter choice |
| Explicit block size gives error at most `α` and information increase at most `α²`; non-small-information tail at `2 I_ext / α` is at most `α` | `SmoothingParameters.lean`: `informationBlockSize_bounds`, `smoothing_at_information_error`, `smoothing_information_le_twice`, `smoothing_tail_at_information`, `small_or_information_smoothing` | Absorbs the additive whole-tape correction without publicizing private seeds |
| Reciprocal-log bias gives `m ≤ 544 k³ log((C+1)/α)³` and corresponding actual communication bound | `SmoothingScale.lean`: `informationBlockSize_polylog_bound`, `smoothing_at_scale` | Quantitative cost budget for the information-inflation smoothing variant |
| Smoothness refers to the smoothed cost and its logarithm stays within a constant original-log factor, for every prospective compression constant | `SmoothingLogBudget.lean`: `smoothingScale_inflation`, `reciprocalBias_le_inflated_scale`, `smoothing_ready_for_compression` | Preprocessing and logarithmic self-consistency for the eventual Theorem 8.5 construction |
| Actual full-transcript simulation interface; identity simulator; external information bounded by communication | `Simulation.lean`: `Simulator`, `identity_simulates`, `externalInformation_le_cost` | Definitions and baseline model checks |
| Actual zero-communication exact simulator when external information is zero | `ZeroInformation.lean`: `zero_information_compression` | Complete zero-information special case of the target |
| Actual zero-communication simulator whenever `I_ext ≤ α²` | `SmallInformation.lean`: `variation_sq_le_divergence`, `average_variation_sq_le`, `small_information_compression` | Quantitative small-information case, including exactly zero information |

Information is measured in nats, and communication in bits. The simulation
interface averages total variation of the input-conditional transcript laws,
and separately bounds disagreement of the two local decoders.

`ExternalCompressionClaim` records the uniform endpoint proposition. Its proof is
`BBCR.externalCompressionClaim` in `Theorem22.lean`; it is not assumed by the
construction or any intermediate result.

## Lemma 8.2 now checked in the finite model

The accumulated Alice/Bob local KL costs are tied to actual execution and their
expectation equals `externalInformation p μ`, after averaging the public seed.
The more general conditional interval identity is also checked: conditioning on
any initial prefix, the expected sum of local divergence costs over the interval
equals the mutual information in the final prefix under that conditional law.
Intervals use zero-based, half-open indices.

The later local kernels continue to use the original prior. The proof shows
that conditioning on a finer history erases the earlier prefix condition; it
does not assume conditional independence or substitute an unrelated channel.
Reached leaves have zero further information and divergence. On null initial
prefixes the measure-theoretic conditional law is zero, and both sides are zero.

The support hypotheses required for real-valued KL are checked before invoking
its nonnegativity. The basic Markov tail bound is for the same protocol's own
external information. The smoothing comparison below now transfers it to the
original protocol's information with an explicit additive correction.

## Smoothing construction now checked

For every finite-seed protocol of cost `C`, every input prior, `0 < β ≤ 1/2`,
and `α > 0`, `smoothing_at_error` constructs an actual simulator with fidelity
error at most `α`, identical public decoders for both parties, and communication
at most `m C`, where

```text
m = ceil_nat(log(2 (C+1) / α) / (2 β²)) + 1.
```

The proof first establishes the input-uniform error bound
`2 (C+1) exp(-2 m β²)`, then verifies the block-size choice. Each player's noise
tape is private and independent of the original seeds. The public decoder reads
block majorities and follows the original tree; even malformed transcripts
decode to a valid original leaf path.

`SmoothingProtocol.smooth_simulation` now proves cost, fidelity, and beta-
smoothness for the same concrete simulator. Smoothness concerns positive-mass
internal prefixes, where a next bit is actually transmitted. Both atoms of the
input-conditional kernel and the observer mixture lie in `[1/2-β, 1/2+β]`.
For `β ≤ 1/4`, the actual reached divergence increment lies in `[0, 8 β]`.

The iid block law is proved equal to the full finite product law. Resampling
the next private correctness bit preserves the private execution law and cannot
change earlier physical messages; flipping that fresh bit flips the next message
at the active sender's node. These facts, rather than an independence assumption
about a conditioned history, establish the probability bounds.

This is an expanded simulation of the original protocol. Its communication
bound is not the information-dependent compression bound of Theorem 2.2.

## Good-event information comparison now checked

Let `G` be the event that both entire correctness-noise tapes have a strict
majority of correct bits at every logical message position, and let `δ = Pr[¬G]`.
`execution_regroup` proves that the actual smoothed execution is the product of
the original input/private-seed experiment and the two new noise tapes.

On `G`, `run_encodedTrace_of_good` reconstructs the entire physical transcript
from the original transcript and noise, using only the public tree. Conditioning
on this event preserves independence and leaves the original experiment's law
unchanged. Data processing therefore gives
`I(input; physical transcript | G, r) ≤ I(input; original transcript | r)` for
each fixed public seed `r`. A null good event gives the zero conditional measure.
The argument retains persistent original private seeds without publicizing them
or assuming fresh intended-message sampling at each node.

On the bad event, the physical tree has at most `2^(m C)` leaf paths, so its
conditional information is at most `m C log 2`. The good/bad flag depends only
on noise and is independent of the input. The checked flag-averaging inequality
and the public-seed average give

```text
I_ext(smoothed, μ) ≤ I_ext(original, μ) + δ m C log 2,
δ ≤ 2 (C+1) exp(-2 m β²).
```

There is no entropy-of-flag term and no seed-cardinality term. The same actual
simulator now satisfies cost, fidelity, beta-smoothness, and this information
bound simultaneously. Applying the existing accumulated-divergence Markov
bound gives, for every `t > 0`,

```text
Pr[D_smoothed ≥ t] ≤
  (I_ext(original, μ) + 2 (C+1) exp(-2 m β²) m C log 2) / t.
```

This is an information-inflation variant of the intermediate smoothing estimate,
not a proof of the paper's exact Lemma 8.4. Its parameter budget is now checked
as described below.

## Information-controlled smoothing parameters now checked

For `0 < α ≤ 1` and `0 < β ≤ 1/2`, `informationBlockSize` is the explicit
natural number

```text
m = ceil_nat(log(2 (C+1)² / (α² β²)) / β²) + 1.
```

`informationBlockSize_bounds` proves that the fidelity bound is at most `α`
and the additive information correction is at most `α²`. The argument uses
`x exp(-2x) ≤ exp(-x)` to absorb the linear factor `m`. The same actual
simulator therefore has error at most `α` and information at most `I_ext + α²`.
The block length obeys
`m ≤ (3 log((C+1)/(α β)) + 2) / β²`, with no unverified ceiling estimate.

The checked `small_or_information_smoothing` gives a zero-communication
simulator when `I_ext ≤ α²`; otherwise the concrete smoothed simulator has
information at most `2 I_ext`. In that regime, `smoothing_tail_at_information`
proves `Pr[D_smoothed ≥ 2 I_ext / α] ≤ α`. The statements also handle `C=0`
and retain arbitrary finite original seed laws.

For `0 < α ≤ 1/2`, put `L = log((C+1)/α)` and `β = 1/(4 k L)`, `k ≥ 1`.
`smoothing_at_scale` checks all guarantees for this choice, including
`C' ≤ 544 k³ L³ C`, where `C'` is the actual smoothed cost. The logarithmic
estimate is `log((C'+1)/α) ≤ (1092 + 6 log k) L`.

For every prospective smooth-compression constant `κ ≥ 1`, the checked choice
`k = (32 κ)²` makes the actual protocol
`1/(κ log((C'+1)/α))`-smooth and gives
`log((C'+1)/α) ≤ 1476 κ L`. Thus both information and the communication
logarithm satisfy constant-factor bounds in terms of the originals. This does
not assume a compressor: `smoothing_ready_for_compression` constructs the
preprocessing simulator for every such `κ`.

## Divergence frontiers and likelihood factorization now checked

The frontier stops at a public leaf or the first point where either player's
sum of local divergences since the starting prefix reaches the chosen threshold.
The finite construction uses the public tree depth as recursion fuel. On actual
complete continuations, the fuel does not create an artificial endpoint: the
stopping test itself holds at the returned endpoint. Endpoints form an
antichain, every complete continuation meets exactly one endpoint, and both
local budgets are strictly below threshold at every strict ancestor.

The four laws are normalized PMFs. The observer follows the actual observer
kernel. Alice's hybrid law follows her local kernel at Alice nodes and the
observer kernel elsewhere; Bob's is analogous. The target follows the actual
sender's local kernel. At each edge, and therefore at every common stopped
endpoint, the laws satisfy

```text
P(w) Q(w) = C(w) D(w).
```

This is the cross-multiplied equation (8.5), with the factorization derived
from the actual kernels rather than supplied as a hypothesis. The cutoff
may depend on both inputs; all four laws use the identical cutoff. The local
kernels retain sender locality, but locating the common frontier still needs
communication in the eventual protocol.

At positive starting prefixes, the target law is proved equal to the original
private-seed execution conditioned on that prefix and stopped there. The
observer law has the same identification for the original joint input/private-
seed experiment. The unnormalized transition proofs include null branches.
These identities require no fresh-private-seed assumption.

All four laws are represented on the same finite endpoint alphabet without
renormalization. For an `ε`-smooth protocol with `ε < 1/2`, observer masses at
every endpoint are positive whenever the starting observer prefix is positive.
Consequently the existing two-party rejection estimates now apply with their
factorization and observer-positivity obligations discharged:
acceptance rate is at least `(1-badMass)/t²`, and the accepted-law total
variation from the target is at most `badMass` when `badMass < 1`.

## Claim 8.9 and a concrete sampling trial now checked

For either player and every reached starting prefix, if `0 < β ≤ 1/4` and the
protocol is β-smooth, the actual target frontier law satisfies

```text
Pr[log(playerFrontier / observerFrontier) ≥ u]
  ≤ exp(-2 (u - 9β)² / (576β)),                 u ≥ 9β.
```

The proof derives local means from the sender's actual conditional KL. The
squared conditional log range is at most `64 KL`, and the stopped drift is at
most `9β`, including the last crossing step. Thus the pathwise squared-width
budget is `576β`. The generic stopped process has exactly the frontier law;
there is no assumed martingale or concentration certificate.

For clipping level `t = exp 1` and `β ≤ 1/18`, union bounding the two tails gives
`badMass ≤ 2 exp(-1/(1152β))`. If
`β ≤ 1/(4608 log((C+1)/α))` and `0 < α ≤ 1/2`, this is at most
`δ = 2 (α/(C+1))⁴ ≤ 1/8`. The accepted frontier law has TV distance at most δ
from the target, is pointwise at most `target/(1-δ)`, and its acceptance rate
is at least `(7/8)/(exp 1)²`.

The actual finite-seed trial is also constructed. Its public randomness samples
a full observer candidate independently of the actual input pair. Each player
computes their own stopping index; their minimum gives the common cutoff. They
exchange binary encodings of the indices and send two independent private
acceptance bits. Each acceptance probability uses only that player's input and
the communicated endpoint. A public decoder recovers the accepted suffix or
`none`. Its law is proved exactly equal to the clipped frontier rejection
trial, not merely close to it. The bit cost is at most
`2 ceil(log₂(C+1)) + 2`, where C is the public tree depth.

The final loop uses the exact likelihood-frontier construction below instead
of iterating this clipped divergence-frontier trial.

## Completed likelihood-frontier route

The earlier divergence-frontier route incurred an unresolved extra logarithm
when multiplying index cost by its `D/β` round bound. The final proof uses a
different stopping rule and an amortized index implementation; it keeps the
single logarithm in the original endpoint.

- `LikelihoodCharge.lean`, `LikelihoodFrontier.lean`: stop at a public leaf or
  the first absolute local log likelihood at least one. Stopped ratios lie in
  `[exp(-2), exp(2)]`. Acceptance is exactly `ρ = 1/(exp 2)²`, and the accepted
  law is exactly the original target frontier. Nonterminal target mass is at
  most four times frontier KL.
- `KernelPotential.lean`, `LikelihoodAccounting.lean`,
  `ResidualInformation.lean`: frontier KL equals the drop in remaining
  information. The initial potential averaged over input and public randomness
  equals `externalInformation` exactly.
- `LazyIndexExchange.lean`, `LikelihoodLocation.lean`, `LikelihoodTrial.lean`,
  `LikelihoodTrialCost.lean`: actual binary communication trees send index
  encodings only when a local cutoff precedes the public leaf. Their expected
  cost is charged to the potential drop, without a reciprocal smoothness factor.
- `FiniteDynamics.lean`, `ProtocolIteration.lean`, `LikelihoodDynamics.lean`,
  `LikelihoodLoop.lean`: finite-table execution, reachability invariants,
  potential budgets, completion probability, actual bit-cost accounting, and
  a fixed bit cutoff. The compiler's seed law is proved equal to the process
  used in the probability bounds.
- `KernelCompletion.lean`, `KernelCoupling.lean`, `LikelihoodCompletion.lean`,
  `LikelihoodSimulation.lean`: terminal payoff invariance, preservation of the
  original continuation law, and total-variation fidelity after truncation.
- `ProtocolFamily.lean`, `LikelihoodSimulator.lean`, `LikelihoodBounds.lean`:
  an actual simulator over the original public seed with independent private
  tables and a common public decoder; average potential becomes information.
- `CompressionParameters.lean`, `CompressionCost.lean`,
  `SmoothCompression.lean`: explicit trial counts, bit cutoffs, error allocation,
  and the single-log information-dependent cost. Small information uses the
  public zero-communication sampler.
- `SimulatorComposition.lean`, `Theorem22.lean`: public decoding composes with
  smoothing, errors add, smoothed information and logarithms are controlled,
  and the uniform endpoint is proved with an explicit constant.

The resulting bound is

```text
cost ≤ K I_ext log((C+1)/α) / α².
```

It is a worst-case depth bound on the actual binary tree, including the local
index messages. Fidelity averages the input-conditional total-variation
errors; it preserves input/transcript correlation. The output alphabet is the
original full public-seed/transcript view. Private randomness remains private.

The endpoint uses an information-inflation variant of smoothing and a different
frontier accounting argument from the paper. It does not claim the exact
intermediate Lemma 8.4 or a formalization of the entire paper. There is no
remaining obligation for the explicitly stated finite-model Theorem 2.2.
Arbitrary infinite measurable random-tape spaces are outside this statement.

## Verification

`lake --wfail build` and `lake lean Audit.lean` are the validation commands.
See `build.log` and `axioms.log` for their recorded outputs. The audited results
use only `propext`, `Classical.choice`, and `Quot.sound`; no mathematical project
axiom or `sorryAx` occurs. Both `theorem_2_2` and `externalCompressionClaim` are included in the audit.

The build reuses pinned dependencies and their existing caches. A fresh-machine
source-only reproduction has not been performed. The older DISJ source files
were not changed for this implementation.
