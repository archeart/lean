module

public import BBCR.PublicInformation
public import BBCR.KernelCoupling

/-! Internal information for arbitrary correlated finite inputs, expressed as
external information after conditioning on each player's known input. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]

noncomputable def alicePrior (μ : PMF (X × Y)) (x : X) : PMF (X × Y) := FiniteCondition.law μ Prod.fst x
noncomputable def bobPrior (μ : PMF (X × Y)) (y : Y) : PMF (X × Y) := FiniteCondition.law μ Prod.snd y

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

/-- Internal information in nats. Each term conditions on the input already
known to the receiver. `internalInformation_eq_condMutualInfo` connects this
finite conditional-law definition to the usual two conditional informations. -/
noncomputable def internalInformation (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) : ℝ :=
  (∑ x, mass (μ.map Prod.fst) x * externalInformation p (alicePrior μ x)) +
  (∑ y, mass (μ.map Prod.snd) y * externalInformation p (bobPrior μ y))

theorem internalInformation_nonneg (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    0 ≤ internalInformation p μ := by
  unfold internalInformation
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro i _ <;>
    exact mul_nonneg (mass_nonneg _ _) (externalInformation_nonneg _ _)

theorem internalInformation_le_twice_cost (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    internalInformation p μ ≤ 2 * p.cost * Real.log 2 := by
  have ha := Finset.sum_le_sum (s := Finset.univ) fun x _ ↦
    mul_le_mul_of_nonneg_left (externalInformation_le_cost p (alicePrior μ x)) (mass_nonneg (μ.map Prod.fst) x)
  have hb := Finset.sum_le_sum (s := Finset.univ) fun y _ ↦
    mul_le_mul_of_nonneg_left (externalInformation_le_cost p (bobPrior μ y)) (mass_nonneg (μ.map Prod.snd) y)
  simp only [← Finset.sum_mul, sum_mass, one_mul] at ha hb
  unfold internalInformation
  linarith

/-- Normalized Theorem 2.1 cost expression. -/
noncomputable def internalCompressionBudget (K I : ℝ) (C : ℕ) (ε : ℝ) : ℝ :=
  K * Real.sqrt ((C : ℝ) * I) * Real.log (((C : ℝ) + 1) / ε) / ε

/-- The uniform finite-model Theorem 2.1 target. This definition is not a proof
and is not supplied as a hypothesis to the construction. -/
def InternalCompressionClaim : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (X Y R SA SB : Type)
    [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [MeasurableSpace R] [DiscreteMeasurableSpace R]
    [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
    [MeasurableSpace SB] [DiscreteMeasurableSpace SB]
    (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) (ε : ℝ),
    0 < ε → ε ≤ 1 / 2 → ∃ s : Simulator p,
      s.Simulates μ ε ∧ s.cost ≤ internalCompressionBudget K (internalInformation p μ) p.cost ε

end BBCR

namespace BBCR.FiniteCondition

variable {A B H : Type} [Fintype A] [Fintype B] [Fintype H]

/-- Exact disintegration over an observed input coordinate, including null
fibers. This identity does not assert independence of correlated inputs. -/
theorem joint_condition (μ : PMF A) (f : A → H) (K : A → PMF B) :
    joint (μ.map f) (fun h ↦ joint (law μ f h) K) =
      (joint μ K).map (fun z ↦ (f z.1,z)) := by
  apply PMF.ext
  rintro ⟨h,a,b⟩
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change mass _ _ = mass _ _
  have hj : mass (joint (μ.map f) (fun h ↦ joint (law μ f h) K)) (h,a,b) =
      mass (μ.map f) h * (mass (law μ f h) a * mass (K a) b) := by
    simp only [mass, joint_apply, ENNReal.toReal_mul]
  rw [hj]
  rw [← mul_assoc, weighted_mass_law, mass_map_sum]
  rw [Fintype.sum_prod_type]
  dsimp only
  simp only [Prod.mk.injEq]
  have he (a' : A) (b' : B) : (f a' = h ∧ a' = a ∧ b' = b) ↔ (a' = a ∧ b' = b ∧ f a = h) := by
    constructor <;> rintro ⟨h₁,h₂,h₃⟩
    · exact ⟨h₂,h₃,h₂ ▸ h₁⟩
    · exact ⟨h₁ ▸ h₃,h₁,h₂⟩
  simp_rw [he, ite_and]
  simp [Finset.sum_ite_eq',ite_mul,mass,joint_apply]

end BBCR.FiniteCondition
