module

public import Disjointness.Protocol

/-!
# Target statement

`FiniteLowerBoundClaim` names the finite-model statement. Its proof is
`Disjointness.finiteLowerBoundClaim` in `LowerBound.lean`; this file only defines
the proposition. `RandomTape.lean` supplies the arbitrary-probability-space extension.
-/

@[expose] public section

namespace Disjointness

abbrev Bits (n : ℕ) := Fin n → Bool

/-- True exactly when the two sets have no common element. -/
def disj {n : ℕ} (x y : Bits n) : Bool :=
  decide (∀ i, x i = false ∨ y i = false)

/-- Finite-model statement, proved in `LowerBound.lean`. Seed cardinalities are unrestricted. -/
def FiniteLowerBoundClaim : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (R SA SB : Type) (_ : Fintype R) (_ : Fintype SA) (_ : Fintype SB)
      (p : Protocol (Bits n) (Bits n) R SA SB),
      p.Correct disj (1 / 3) → a * (n : ℝ) ≤ (p.cost : ℝ)

end Disjointness
