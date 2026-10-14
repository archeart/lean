# Status

Updated 2026-10-14. **Phases 1–7 complete for the stated public-output tree models.**

## Proved endpoints

The explicit constant is `lowerBoundConstant = 1 / (144 * Real.log 2) > 0`.
For every dimension, including zero, and worst-case error at most `1/3`:

- `Protocol.and_information_lower_bound`: one-coordinate AND information is at least `1/144` nats.
- `Protocol.bjks_information_lower_bound`: `n / 144 ≤ J(Π)`.
- `disjointness_lower_bound`: `n / (144 log 2) ≤ cost Π` for the finite-seed model.
- `finiteLowerBoundClaim`: proves the original target proposition, with threshold `n₀ = 0`.
- `disjointness_lower_bound_of_length`: the same bound for any uniform bound on actual execution lengths; unreachable deep branches do not weaken the result.
- `random_tape_disjointness_lower_bound`: the same bound for measurable bounded deterministic behaviors selected from an arbitrary probability space, including atomless random tapes.
- `random_tree_disjointness_lower_bound`: allows tape-indexed trees with unreachable deep branches; truncation and finite behavior encoding preserve execution within the given length bound.

The information chain is checked end to end:

`n / 144 ≤ I((X,Y);T | D,R) ≤ cost Π * log 2`.

## Where to review

| Step | File and principal declarations |
| --- | --- |
| Protocol semantics | `Protocol.lean`: `Tree.run`, `Protocol.Correct`, `Protocol.cost` |
| Nonempty model | `SendInput.lean`: `sendInputProtocol_correct`, `sendInputProtocol_cost` |
| Locality and rectangles | `Tree.lean`, `Factorization.lean`: `run_transcript_eq_iff`, `viewLaw_factorization` |
| Switch law | `Switch.lean`: `law`, `law_map_triples`, `disj_of_mem_support`, conditional independence |
| Information upper bound | `InformationCost.lean`, `ExecutionConditioning.lean`: `bjksInformationCost_le` |
| Distance inequalities | `Hellinger.lean`: `sqDist_triangle`, `variation_sq_le`, `cut_and_paste`, `sqDist_le_two_jensenShannon` |
| Exact information bridge | `BinaryInformation.lean`, `FiniteView.lean`, `ChannelBridge.lean`: `information_fair`, `informationCost_eq_channel` |
| AND bound | `AndLowerBound.lean`: `and_information_lower_bound` |
| Coordinate decomposition | `CoordinateInformation.lean`: `bjksInformationCost_ge_sum_coordinates` |
| Actual embedded protocols | `LocalRandomization.lean`, `Embedding.lean`: `embed`, `embed_correct`, `embed_cost` |
| Exact embedding laws | `ProductReplacement.lean`, `EmbeddingInformation.lean`: `inputLaw_fill`, `joint_fill_channel`, `embed_informationCost` |
| Linear bounds | `LowerBound.lean`: `bjks_information_lower_bound`, `disjointness_lower_bound`, `finiteLowerBoundClaim` |
| Normalization | `ReachableCost.lean`, `RandomTape.lean`: `run_truncate`, `toTree_encode`, random-tape endpoints |

## Audit and reproduction

`Audit.lean` prints the endpoint types and transitive axioms. Only `propext`,
`Classical.choice`, and `Quot.sound` occur in the inspected proof chain. No
`sorryAx`, mathematical project axiom, `admit`, or `native_decide` is used.
See `audit.md`, `axioms.log`, and `clean-build.log` for the final checks.
Dependencies remain pinned; no upgrades or additional installation were needed.

The API documentation and interactive blueprint are available through
`./scripts/explore open`; rebuild them with `./scripts/explore build`.

## Exact scope

Local communication is binary and interactive. Every internal node transmits one
bit; speaker choice and stopping are determined by the public tree and history.
The output is the reached leaf label. Correctness averages over randomness and
holds separately on every input. Random bits are free.

The finite theorem has no bound on seed cardinalities or seed probabilities.
The random-tape theorem removes finite-randomness restrictions by a proved finite
behavior pushforward; its explicit hypothesis is measurability of that behavior.
The length bound holds for every tape and input, rather than only almost surely.

A translation from a particular machine-level protocol language is not formalized.
Neither is the separate convention where only one player knows the answer: that
comparison requires a proved final-answer-bit simulation and its additive overhead.
Expected communication, nonpublic stopping, and quantum protocols are outside scope.
