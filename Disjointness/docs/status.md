# Status

Updated 2026-10-14. **Phases 1–2 complete; Phase 3 next.**

## Checked results

`lake --wfail build` passes after cleaning this project's build output. All seven
results in `Disjointness/Integration.lean` have only the ordinary foundational axioms
`propext`, `Classical.choice`, and `Quot.sound` in their transitive dependencies:

| Declaration (namespace `Disjointness.Integration`) | Checked mathematical content |
| --- | --- |
| `pmf_chain_rule` | The entropy chain rule on PMF-derived measure spaces |
| `pmf_condMutualInfo_nonneg` | Nonnegative conditional mutual information |
| `pmf_condMutualInfo_le_log_card` | Information at most log of transcript alphabet size |
| `pmf_condMutualInfo_eq_sum` | Finite averaging over a conditioning variable, including null events |
| `pmf_condEntropy_pair_le` | Conditional entropy subadditivity for two variables |
| `pmf_condMutualInfo_bitvec_le` | A `c`-bit-vector alphabet gives an upper bound `c * log 2` in nats |
| `pmf_klDiv_eq_zero_iff` | Mathlib KL vanishes exactly when the two PMFs are equal |

These reuse PFR/mathlib theorems. They establish dependency compatibility and a
small part of the required adapters, not protocol information bounds.

`Protocol.lean` checks the tree/execution, independent seed sampling, output law,
pointwise error, and cost definitions. `Target.lean` checks the syntax and types of
the finite-model endpoint. `FiniteLowerBoundClaim` is a proposition definition,
not a theorem or an assumed fact.

## Checked protocol results (Phase 2)

| Declaration | Mathematical content |
| --- | --- |
| `Tree.decode_run` | The public tree and bit transcript determine the output |
| `Tree.run_length_le_depth` | Each execution uses at most the tree depth in transmitted bits |
| `Tree.run_transcript_eq_iff` | A transcript fiber factors into Alice-only and Bob-only consistency conditions |
| `Tree.transcript_cross` | Standard deterministic rectangle crossing property |
| `Tree.run_mem_leafPaths`, `Tree.card_leafPaths_le` | Every execution is a leaf path; a depth-`c` tree has at most `2^c` such paths |
| `Protocol.privateTranscriptLaw_factorization` | Fixed-public-seed transcript probabilities equal `A(r,t,x) * B(r,t,y)` |
| `Protocol.viewLaw_apply`, `Protocol.viewLaw_factorization` | The joint public-seed/transcript law agrees with execution and includes the public-seed probability factor |
| `Protocol.privateTranscriptLaw_support`, `Protocol.card_leafPaths_le_cost` | A uniform support bound for each public seed, independent of the seed cardinality |
| `sendInputProtocol_correct`, `sendInputProtocol_cost` | A concrete zero-error DISJ protocol of cost `n+1` for every `n` |

All of these follow from the definitions; rectangle structure and information
bounds were not assumed as protocol fields. The send-input construction proves
that the class of correct DISJ protocols is nonempty in every dimension. Its extra
bit is Bob's public answer.

## Milestone evidence

- Lean v4.35.0-rc4 installed with exact PFR/mathlib revisions and a transitive lockfile.
- The imported PFR modules compiled against cached mathlib dependencies.
- A clean rebuild of the seven project modules passed with warnings treated as failures.
- `Audit.lean` prints the exact target and the axiom sets; see `axioms.log`.
- `blueprint.md` fixes the dependency graph, key interfaces, candidate constants,
  and open protocol-model bridges. `decisions.md` records the representation choice.

## Human audit focus

Read `Target.lean` and the endpoint/model section of `blueprint.md`. In particular,
cost currently means maximum tree depth, and all random-seed laws are finite. The
bridges to conventional worst-case communication and arbitrary random tapes are
named outstanding obligations; no conventional public-coin theorem is claimed yet.

## Next action

Phase 3: construct the switch/input law, prove its conditional independence properties,
define the exact protocol information cost `J`, and connect the leaf support bounds
to `J ≤ cost * log 2` without charging public randomness.

## Unproved obligations

The switch distribution properties, the protocol information upper bound, Hellinger/AND lower bound,
coordinate embeddings, DISJ lower bound, and conventional-model bridges remain unproved.
