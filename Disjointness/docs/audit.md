# Final audit record

## Result and quantifiers

`Disjointness.finiteLowerBoundClaim` proves the proposition originally defined in
`Target.lean`. The chosen constants are `a = 1 / (144 * log 2)` and `n₀ = 0`.
They precede all dimensions, seed types, seed laws, and protocols. The finite
protocol theorem requires only finite seed types and worst-case correctness at
error `1/3`; discrete measurable spaces are installed inside its proof, not
imposed as an extra endpoint hypothesis.

`random_tree_disjointness_lower_bound` further permits an arbitrary probability
space of tapes. The source is a tape-indexed deterministic local communication
tree, with a bound `c` on every actual input/tape execution. The explicit
measurability assumption concerns its bounded behavior encoding. The conclusion
is `a * n ≤ c`. Thus finite randomness and unreachable deep branches are no longer
unproved normalization obligations for this stated source model.

## Separate semantic review

This review was performed by the same agent after the endpoint compiled; it is
not an independent human review or a second-model review.

- **No conclusion hidden in the model:** `Protocol` contains three seed laws and
  a public-seed-indexed local tree. It contains no rectangle, entropy, distance,
  correctness, or lower-bound assumption. These are proved from execution.
- **Nonvacuity:** `sendInputProtocol_correct` gives a zero-error DISJ protocol in
  every dimension, with `sendInputProtocol_cost = n+1`.
- **Locality:** an Alice node receives only Alice's augmented input; a Bob node
  receives only Bob's. A node's speaker and the presence of a leaf are public.
  There is no free signaling through private stopping or uncharged control flow.
- **Error:** `Correct` quantifies over all input pairs. It averages over all three
  seed laws. The AND separation uses both `00` and `11`; the latter is outside
  the information distribution's support. No fixed public seed is assumed correct.
- **Analysis switches:** `communicated` never reads `D`. Each embedded protocol
  fixes padding switches as public parameters, but the actual selected-coordinate
  switch exists only in the information experiment. Its padding bit at the selected
  coordinate is overwritten, so the fixed parameter there has no effect.
- **Private padding:** `localRandomize` is an actual tree protocol with independent
  private seed pairs. `localRandomize_seedLaw`, `inputLaw_fill`, and
  `joint_fill_channel` prove the sampling laws. `embed_correct` proves correctness
  on every AND input; `embed_informationCost` proves the required information identity.
- **Public randomness:** `informationCost_eq_view` moves `R` from conditioning to
  the view using independence of `(inputs,D)` and `R`. It does not charge `H(R)`.
  Null public seeds are handled by the conditional-measure results in Phase 3.
- **Information:** all mutual and conditional information is PFR information in
  nats. The finite entropy formulas and Jensen–Shannon identity are proved adapters,
  not an alternative information functional with assumed properties.
- **Distance normalization:** `sqDist` is one half of the sum of squared square-root
  differences; `variation` is one half of the absolute mass differences. The proof
  obtains `TV² ≤ 2 h²`, `h²(00,11) ≤ 8 J`, and `TV(00,11) ≥ 1/3`, giving `J ≥ 1/144`.
- **Coordinate sum:** input coordinate independence is proved under each switch
  fiber; conditional entropy subadditivity gives the information inequality.
  Coordinate terms use the equivalent `(R,T)` view formulation. The exact identity
  used by the assembly is in `embed_informationCost`, followed by `average_resample`.
- **Cost:** the original finite theorem uses maximum tree depth. `run_truncate`
  proves that truncating at any uniform actual-length bound preserves execution,
  and `truncate_cost_le` supplies the matching depth bound.
- **Arbitrary tapes:** `BoundedTree.Code` enumerates finite bounded local behaviors
  because the input sets and depth are finite. `encode` is a concrete truncating
  encoding, `toTree_encode` identifies its execution tree, and a measurable
  pushforward to this finite type preserves exact error probabilities. No bound
  on the original tape space or number of random bits is assumed.
- **Small dimensions:** the coordinate sum is empty at `n=0`; the endpoint includes
  it directly. Positivity of `log 2` and of the stated constant is proved.

## Foundations and axiom inspection

`lake env lean Audit.lean` prints transitive axioms for the original interfaces,
major analytic results, all public Phase 5–7 theorems, and the final endpoint types.
Every inspected axiom list is a subset of
`{propext, Classical.choice, Quot.sound}`. The final output is `axioms.log`;
`phase4-axioms.log` preserves the earlier AND checkpoint.

Source review found no proof holes, unproved mathematical project axioms,
`admit`, or `native_decide`. PFR disables its own `sorry` warning, so the endpoint's
transitive axiom inspection is essential even when the build has no warnings.

Lean's kernel checks proof terms against the pinned imported declarations. This
is not a formal verification of the Lean compiler, host operating system, or
artifact-distribution infrastructure.

## Reproduction

Run from the project directory with elan on `PATH`:

```sh
lake clean disjointness
lake --wfail build
lake env lean Audit.lean
./scripts/explore build
```

The final clean project rebuild and audit passed. `clean-build.log` and
`axioms.log` retain their outputs; `explorer-build.log` records API/blueprint
rebuilding and declaration-link validation. Preserve `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. Do not update dependencies during reproduction.

This is a clean project rebuild using the pinned dependency cache, not an
independent fresh-machine or complete source-only rebuild of mathlib. Imported
PFR source modules and the project compiled locally; mathlib artifacts came from
its compiled cache. Documentation renderer warnings are separate from the
warning-free Lean library build.

## Remaining boundaries

The result is a randomized interactive communication lower bound in the explicitly
stated local-tree model, including arbitrary measurable public random tapes.
It does not include a translation from another formal machine or protocol syntax.
It uses a public leaf output. A private-output-only convention would require a
separate answer-bit simulation and an adjusted threshold/constant. This extension
has not been silently folded into the endpoint. Almost-sure length bounds, expected
communication, and nonclassical protocols are not claimed.
