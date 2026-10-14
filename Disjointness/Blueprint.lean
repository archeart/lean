import Architect
import Disjointness

/-!
Blueprint metadata lives here so documentation can evolve without changing the
mathematical source files. Attributes below describe existing declarations;
they introduce no new mathematical statements or assumptions.
-/

attribute [blueprint "def:tree"
  (title := "Binary communication trees")
  (statement := /-- A finite binary tree has publicly labeled leaves. At an Alice
  node the next bit depends only on Alice's augmented input; at a Bob node it
  depends only on Bob's augmented input. -/)] Disjointness.Tree

attribute [blueprint "def:execution"
  (title := "Execution and transcript")
  (statement := /-- Executing a tree on augmented inputs returns the list of
  transmitted bits together with the Boolean output at the reached leaf. -/)]
  Disjointness.Tree.run

attribute [blueprint "def:protocol"
  (title := "Randomized protocols")
  (statement := /-- A public seed selects a communication tree. Public randomness
  and the two private seeds have independent probability laws; no bound on seed
  cardinalities is built into this definition. -/)] Disjointness.Protocol

attribute [blueprint "def:correct"
  (title := "Pointwise correctness")
  (statement := /-- A protocol is correct with error at most $\varepsilon$ if,
  for every input pair, its probability of an incorrect output is at most
  $\varepsilon$. The probability averages over all protocol seeds. -/)]
  Disjointness.Protocol.Correct

attribute [blueprint "def:cost"
  (title := "Communication cost")
  (statement := /-- For a finite public seed type, cost is the maximum tree depth
  over public seeds. This counts even unreachable branches; the proved truncation bridge transfers the bound to
  worst-case reachable execution lengths. -/)]
  Disjointness.Protocol.cost

attribute [blueprint "def:disj"
  (title := "Set disjointness")
  (statement := /-- For $x,y\in\{0,1\}^n$, $\operatorname{DISJ}(x,y)$ is true
  exactly when no coordinate is true in both inputs. -/)] Disjointness.disj

attribute [blueprint "thm:decode"
  (title := "The transcript determines the output")
  (statement := /-- Decoding the transcript of an execution in its public tree
  returns that execution's output. -/)
  (proof := /-- Induction on the communication tree. -/)]
  Disjointness.Tree.decode_run

attribute [blueprint "thm:rectangle"
  (title := "Transcript rectangles")
  (statement := /-- A pair of augmented inputs produces a given transcript if
  and only if Alice's input is Alice-consistent with that transcript and Bob's
  input is Bob-consistent with it. Thus each transcript fiber is a rectangle. -/)
  (proof := /-- Induction on the tree, splitting on the transmitted bit. -/)]
  Disjointness.Tree.run_transcript_eq_iff

attribute [blueprint "thm:leaves"
  (title := "Leaf transcript bound")
  (statement := /-- A binary tree of depth $c$ has at most $2^c$ distinct leaf
  transcripts. -/)
  (proof := /-- Induction on the tree; prefixing the bit separates the two
  branches, and their cardinalities add. -/)] Disjointness.Tree.card_leafPaths_le

attribute [blueprint "thm:factorization"
  (title := "Transcript probability factorization")
  (statement := /-- For finite private seed types, fixed public seed $r$, inputs
  $x,y$, and transcript $t$, its probability factors as
  $\Pr[T=t\mid x,y,r]=A(r,t,x)B(r,t,y)$. -/)
  (proof := /-- Apply the rectangle characterization and independence of the
  private seed laws to factor the finite probability sum. -/)]
  Disjointness.Protocol.privateTranscriptLaw_factorization

attribute [blueprint "thm:support"
  (title := "Transcript support bound")
  (statement := /-- For every public seed $r$, the number of leaf transcripts
  is at most $2^{\operatorname{cost}(\Pi)}$. Together with the checked support
  lemma, this bounds the support of the fixed-seed transcript law. -/)
  (proof := /-- Combine the leaf bound with the fact that the selected tree's
  depth is at most the protocol cost. -/)]
  Disjointness.Protocol.card_leafPaths_le_cost

attribute [blueprint "thm:example"
  (title := "A concrete correct DISJ protocol")
  (statement := /-- Sending all $n$ input bits and then the answer bit gives a
  DISJ protocol with zero error and cost $n+1$. This witnesses that the class of
  correct protocols is nonempty in every dimension. -/)
  (proof := /-- The checked send-input construction computes DISJ and its tree
  has depth $n+1$. -/)]
  Disjointness.sendInputProtocol_correct Disjointness.sendInputProtocol_cost

attribute [blueprint "thm:entropy"
  (title := "An entropy library adapter")
  (statement := /-- For a finite transcript alphabet $B$, the checked PMF adapter
  bounds conditional mutual information by $\log |B|$, in nats. This is an
  alphabet bound; the protocol theorem uses a fiberwise support version. -/)
  (proof := /-- Reuse the PFR conditional-information bound through the PMF
  to probability-measure adapter. -/)]
  Disjointness.Integration.pmf_condMutualInfo_le_log_card

attribute [blueprint "def:switch"
  (title := "The switch and input distribution")
  (statement := /-- Sample independent fair switches. Conditional on a false
  switch, Alice's bit is zero and Bob's bit is fair; for a true switch their roles
  reverse. Coordinates are sampled independently. -/)] Disjointness.Switch.law

attribute [blueprint "thm:switch"
  (title := "Switch distribution properties")
  (statement := /-- The input marginal at each coordinate is
  $(00,01,10,11)\mapsto(1/2,1/4,1/4,0)$. Inputs in the support are disjoint.
  Conditional on the switches, the coordinate pairs are independent and the
  players' input vectors are independent. -/)
  (proof := /-- Explicit finite product laws, conditional-fiber identities,
  and the independence of product measures. -/)]
  Disjointness.Switch.law_map_coordinate Disjointness.Switch.coordinate_input_probabilities
  Disjointness.Switch.disj_of_mem_support
  Disjointness.Switch.coordinates_condIndep Disjointness.Switch.players_condIndep

attribute [blueprint "def:information"
  (title := "BJKS conditional information cost")
  (statement := /-- $J(\Pi)=I((X,Y);T\mid D,R)$ in nats, with inputs from the
  switch distribution and independent public and private protocol seeds.
  $T$ is the actual execution transcript; $D$ is not supplied to the protocol. -/)]
  Disjointness.Protocol.bjksInformationCost

attribute [blueprint "thm:conditioning"
  (title := "Public seeds preserve the conditional input law")
  (statement := /-- Conditional on $D=d,R=r$, for every public seed of positive
  probability, the input law is exactly the switch-conditioned product law.
  In particular the coordinate pairs remain independent under the conditioning
  used in $J$. Null public-seed fibers have zero conditional measure. -/)
  (proof := /-- Regroup the finite joint law into conditioning variables and
  remaining randomness, then evaluate the conditional fibers. -/)]
  Disjointness.Protocol.conditional_inputLaw Disjointness.Protocol.bjks_coordinates_condIndep
  Disjointness.Protocol.conditional_zero_of_publicLaw_zero

attribute [blueprint "thm:upper"
  (title := "Communication bounds conditional information")
  (statement := /-- Every finite protocol satisfies
  $0\leq J(\Pi)\leq\operatorname{cost}(\Pi)\log 2$.
  This uses no correctness assumption and charges no public-seed entropy. -/)
  (proof := /-- Bound information by conditional transcript entropy. On each
  $(D,R)$ fiber, execution lies in the public tree's leaf set, of cardinality at
  most $2^{\operatorname{cost}(\Pi)}$. Average the entropy bounds. -/)]
  Disjointness.Protocol.bjksInformationCost_nonneg Disjointness.Protocol.bjksInformationCost_le

attribute [blueprint "def:hellinger"
  (title := "Squared Hellinger distance")
  (statement := /-- The squared distance is one half of the sum of squared
  differences of square-root point masses. -/)] Disjointness.Hellinger.sqDist

attribute [blueprint "thm:distances"
  (title := "Finite distance comparisons")
  (statement := /-- Squared Hellinger distance satisfies the squared triangle
  estimate. Total variation satisfies $\mathrm{TV}^2\leq 2h^2$ and bounds
  differences in event probabilities. -/)
  (proof := /-- Finite-sum inequalities and Cauchy--Schwarz. -/)]
  Disjointness.Hellinger.sqDist_triangle Disjointness.Hellinger.variation_sq_le
  Disjointness.Hellinger.event_difference_le

attribute [blueprint "thm:binary"
  (title := "Binary information controls distance")
  (statement := /-- For a fair binary selector, $h^2(P,Q)\leq 2I$ in nats. -/)
  (proof := /-- A scalar logarithm inequality gives the Jensen--Shannon
  comparison; the entropy formula identifies it with PFR mutual information. -/)]
  Disjointness.Channel.sqDist_le_two_information_fair

attribute [blueprint "thm:view"
  (title := "Exact finite channel bridge")
  (statement := /-- The finite channel expression for $I((X,Y);(R,T)\mid D)$
  equals the protocol's $I((X,Y);T\mid D,R)$. -/)
  (proof := /-- Independence of public randomness moves it into the observed
  view; exact joint-law identities preserve conditional information. -/)]
  Disjointness.Protocol.informationCost_eq_channel

attribute [blueprint "thm:and"
  (title := "AND requires positive information")
  (statement := /-- Every finite randomized AND protocol with worst-case error
  at most $1/3$ has conditional information cost at least $1/144$ nats. -/)
  (proof := /-- Transcript factorization gives cut-and-paste. Correctness at
  $00$ and $11$ separates the joint seed/transcript laws; the distance and
  binary-information bounds yield the stated constant. -/)]
  Disjointness.Protocol.and_information_lower_bound

attribute [blueprint "thm:coordinates"
  (title := "Coordinate information decomposition")
  (statement := /-- Total conditional information dominates the sum of the
  coordinate information terms under the switch distribution. -/)
  (proof := /-- Entropy additivity for independent input coordinates and
  conditional entropy subadditivity. -/)]
  Disjointness.Protocol.bjksInformationCost_ge_sum_coordinates

attribute [blueprint "def:embed"
  (title := "Actual embedded AND protocols")
  (statement := /-- Fix padding switches as public parameters, sample the
  players' padding independently, insert the two AND input bits, execute DISJ,
  and negate its answer. -/)] Disjointness.Protocol.embed

attribute [blueprint "thm:embedding"
  (title := "Correctness and exact information of embeddings")
  (statement := /-- The embedded protocol computes AND on all four inputs,
  preserves communication, and has information cost equal to the average
  of the two selected-switch coordinate terms. -/)
  (proof := /-- Prove exact seed regrouping and product-replacement laws.
  Padding is disjoint; joint-law invariance gives the information identity. -/)]
  Disjointness.Protocol.embed_correct Disjointness.Protocol.embed_cost
  Disjointness.Protocol.embed_informationCost

attribute [blueprint "thm:lower"
  (title := "Linear DISJ information lower bound")
  (statement := /-- Every correct DISJ protocol has $J(\Pi)\geq n/144$ nats. -/)
  (proof := /-- Apply the AND theorem to every embedding, average over padding
  switches, and sum the coordinate information inequalities. -/)]
  Disjointness.Protocol.bjks_information_lower_bound

attribute [blueprint "thm:target"
  (title := "Finite-model communication lower bound")
  (statement := /-- At worst-case error $1/3$, every finite-seed protocol has
  communication at least $n/(144\log 2)$ bits. This includes $n=0$ and imposes
  no restriction on seed cardinalities. -/)
  (proof := /-- Combine the information lower and upper bounds and divide
  by the positive constant $\log 2$. -/)]
  Disjointness.disjointness_lower_bound Disjointness.finiteLowerBoundClaim

attribute [blueprint "thm:reachable"
  (title := "Reachable-length normalization")
  (statement := /-- The same lower bound holds for any uniform bound on actual
  execution lengths, regardless of unreachable branches. -/)
  (proof := /-- Truncation at that bound preserves every actual execution
  and gives a protocol with bounded tree depth. -/)]
  Disjointness.disjointness_lower_bound_of_length

attribute [blueprint "thm:tapes"
  (title := "Arbitrary measurable random tapes")
  (statement := /-- The linear lower bound holds for local trees chosen from
  an arbitrary probability space of random tapes, with measurable bounded
  behavior and worst-case execution length at most $c$. -/)
  (proof := /-- Encode each truncated tree in a finite bounded-behavior type.
  Push the tape measure forward to this finite public-seed law, preserving
  correctness exactly, and apply the finite-model theorem. -/)]
  Disjointness.random_tree_disjointness_lower_bound
