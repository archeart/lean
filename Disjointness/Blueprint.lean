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
  over public seeds. This counts even unreachable branches; comparison with
  conventional worst-case reachable cost remains a separate proof obligation. -/)]
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
  alphabet bound; connecting it to protocol cost is still unfinished. -/)
  (proof := /-- Reuse the PFR conditional-information bound through the PMF
  to probability-measure adapter. -/)]
  Disjointness.Integration.pmf_condMutualInfo_le_log_card
