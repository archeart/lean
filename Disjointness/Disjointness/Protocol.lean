module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite binary protocols

Public history is represented by the current tree node. Local decisions only see
the player's own augmented input. Random seeds have arbitrary finite laws.

This file defines the model for review. `Tree.lean` and `Factorization.lean` prove
rectangle structure and transcript support. The relationship to conventional
random-tape protocols remains an open normalization obligation.
-/

@[expose] public section

namespace Disjointness

/-- A finite public communication tree with one transmitted bit per internal node. -/
inductive Tree (A B : Type*) where
  | leaf (output : Bool)
  | alice (message : A → Bool) (zero one : Tree A B)
  | bob (message : B → Bool) (zero one : Tree A B)

namespace Tree

variable {A B : Type*}

/-- The maximum number of transmitted bits along a tree path. -/
def depth : Tree A B → ℕ
  | .leaf _ => 0
  | .alice _ zero one => max zero.depth one.depth + 1
  | .bob _ zero one => max zero.depth one.depth + 1

/-- Execute the tree, returning the communicated bit path and the public output. -/
def run : Tree A B → A → B → List Bool × Bool
  | .leaf output, _, _ => ([], output)
  | .alice message zero one, a, b =>
      let bit := message a
      let result := if bit then one.run a b else zero.run a b
      (bit :: result.1, result.2)
  | .bob message zero one, a, b =>
      let bit := message b
      let result := if bit then one.run a b else zero.run a b
      (bit :: result.1, result.2)

end Tree

/-- Independent public/private random seeds, followed by a public-seed-indexed tree.
Finiteness is imposed by the endpoint, not hidden in the fields. -/
structure Protocol (X Y R SA SB : Type*) where
  publicLaw : PMF R
  aliceLaw : PMF SA
  bobLaw : PMF SB
  tree : R → Tree (X × SA) (Y × SB)

namespace Protocol

variable {X Y R SA SB : Type*}

/-- All seeds are sampled independently of each other and of the input. -/
noncomputable def seedLaw (p : Protocol X Y R SA SB) : PMF (R × (SA × SB)) :=
  p.publicLaw.bind fun r ↦
    p.aliceLaw.bind fun a ↦ p.bobLaw.map fun b ↦ (r, a, b)

/-- Joint public-seed/transcript law for a fixed input. -/
noncomputable def viewLaw (p : Protocol X Y R SA SB) (x : X) (y : Y) :
    PMF (R × List Bool) :=
  p.seedLaw.map fun s ↦ (s.1, ((p.tree s.1).run (x, s.2.1) (y, s.2.2)).1)

/-- Output law for a fixed input. -/
noncomputable def outputLaw (p : Protocol X Y R SA SB) (x : X) (y : Y) : PMF Bool :=
  p.seedLaw.map fun s ↦ ((p.tree s.1).run (x, s.2.1) (y, s.2.2)).2

/-- Pointwise error, in real probability units. -/
noncomputable def error (p : Protocol X Y R SA SB) (f : X → Y → Bool) (x : X) (y : Y) : ℝ :=
  (p.outputLaw x y (!(f x y))).toReal

/-- Correctness includes every input pair, not only the support of an analysis law. -/
def Correct (p : Protocol X Y R SA SB) (f : X → Y → Bool) (ε : ℝ) : Prop :=
  ∀ x y, p.error f x y ≤ ε

/-- Uniform tree-depth bound, including all public seeds and tree branches.
The bridge from a bound on reachable transcripts is a separate obligation. -/
def cost [Fintype R] (p : Protocol X Y R SA SB) : ℕ :=
  Finset.univ.sup fun r ↦ (p.tree r).depth

end Protocol

end Disjointness
