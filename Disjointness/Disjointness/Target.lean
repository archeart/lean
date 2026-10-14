module

public import Disjointness.Protocol

/-!
# Target statement

`FiniteLowerBoundClaim` is a proposition naming the finite-model target. It is not
a theorem or an axiom, and nothing here asserts that it holds. The conventional
public-coin claim additionally requires the normalization bridges in the blueprint.
-/

@[expose] public section

namespace Disjointness

abbrev Bits (n : ℕ) := Fin n → Bool

/-- True exactly when the two sets have no common element. -/
def disj {n : ℕ} (x y : Bits n) : Bool :=
  decide (∀ i, x i = false ∨ y i = false)

/-- Precise finite-model target, awaiting proof. Seed cardinalities are unrestricted. -/
def FiniteLowerBoundClaim : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (R SA SB : Type) (_ : Fintype R) (_ : Fintype SA) (_ : Fintype SB)
      (p : Protocol (Bits n) (Bits n) R SA SB),
      p.Correct disj (1 / 3) → a * (n : ℝ) ≤ (p.cost : ℝ)

end Disjointness
