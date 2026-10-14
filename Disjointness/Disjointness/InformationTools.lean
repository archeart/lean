module

public import Disjointness.Integration

/-! Entropy adapters with finite sample spaces and potentially infinite transcript alphabets. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Disjointness.InformationTools

local instance {E F : Type*} [Finite E] (f : E → F) : FiniteRange f :=
  ⟨Set.finite_range f⟩

variable {Ω A B C : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Countable B] [MeasurableSingletonClass B]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

/-- Conditional chain rule, including nonfinite alphabets with finite range. -/
theorem cond_chain (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    condEntropy (fun ω ↦ (X ω, Y ω)) Z μ =
      condEntropy X Z μ + condEntropy Y (fun ω ↦ (X ω, Z ω)) μ :=
  cond_chain_rule' μ .of_discrete .of_discrete .of_discrete

theorem cond_pair_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    condEntropy (fun ω ↦ (X ω, Y ω)) Z μ ≤
      condEntropy X Z μ + condEntropy Y Z μ := by
  have h := condMutualInfo_nonneg (μ := μ) (Z := Z)
    (show Measurable X from .of_discrete) (show Measurable Y from .of_discrete)
  rw [condMutualInfo_eq .of_discrete .of_discrete .of_discrete] at h
  exact sub_nonneg.mp h

/-- Information depends only on the joint law of the three variables. -/
theorem condMutualInfo_identDistrib {Ω' : Type*} [Fintype Ω']
    [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C)
    (X' : Ω' → A) (Y' : Ω' → B) (Z' : Ω' → C)
    (h : IdentDistrib (fun ω ↦ (X ω, (Y ω, Z ω)))
      (fun ω ↦ (X' ω, (Y' ω, Z' ω))) μ ν) :
    condMutualInfo X Y Z μ = condMutualInfo X' Y' Z' ν := by
  rw [condMutualInfo_eq' .of_discrete .of_discrete .of_discrete,
    condMutualInfo_eq' .of_discrete .of_discrete .of_discrete]
  congr 1
  · exact IdentDistrib.condEntropy_eq .of_discrete .of_discrete .of_discrete .of_discrete
      (h.comp (show Measurable (fun z : A × (B × C) ↦ (z.1, z.2.2)) from .of_discrete))
  · exact IdentDistrib.condEntropy_eq .of_discrete .of_discrete .of_discrete .of_discrete h

omit [Fintype Ω] in
/-- A fiberwise support bound controls conditional entropy without charging the
cardinality (or entropy) of the conditioning variable. Null fibers contribute zero. -/
theorem condEntropy_le_of_fiber_support (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → B) (Z : Ω → C) (S : C → Finset B) (c : ℕ)
    (hS : ∀ ω, T ω ∈ S (Z ω)) (hcard : ∀ z, (S z).card ≤ 2 ^ c) :
    condEntropy T Z μ ≤ (c : ℝ) * Real.log 2 := by
  classical
  rw [condEntropy_eq_sum_fintype _ _ _ .of_discrete]
  have hbound (z : C) : entropy T (μ[|Z ⁻¹' {z}]) ≤ (c : ℝ) * Real.log 2 := by
    have hmem : ∀ᵐ ω ∂μ[|Z ⁻¹' {z}], T ω ∈ S z :=
      ae_cond_of_forall_mem (.of_discrete) (fun ω hω ↦ by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hω ▸ hS ω)
    have he := entropy_le_log_card_of_mem (show Measurable T from .of_discrete) hmem
    by_cases hz : (S z).card = 0
    · simp only [hz, Nat.cast_zero, Real.log_zero] at he
      exact he.trans (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
    · refine he.trans ?_
      calc
        Real.log (S z).card ≤ Real.log ((2 : ℝ) ^ c) :=
          Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hcard z)
        _ = (c : ℝ) * Real.log 2 := Real.log_pow _ _
  calc
    _ ≤ ∑ z, μ.real (Z ⁻¹' {z}) * ((c : ℝ) * Real.log 2) :=
      Finset.sum_le_sum (fun z _ ↦ mul_le_mul_of_nonneg_left (hbound z) (measureReal_nonneg))
    _ = (c : ℝ) * Real.log 2 := by
      rw [← Finset.sum_mul, sum_measureReal_preimage_singleton _ (fun _ _ ↦ .of_discrete)]
      simp

theorem condMutualInfo_le_of_fiber_support (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (T : Ω → B) (Z : Ω → C) (S : C → Finset B) (c : ℕ)
    (hS : ∀ ω, T ω ∈ S (Z ω)) (hcard : ∀ z, (S z).card ≤ 2 ^ c) :
    condMutualInfo X T Z μ ≤ (c : ℝ) * Real.log 2 := by
  rw [condMutualInfo_comm .of_discrete .of_discrete Z μ,
    condMutualInfo_eq' .of_discrete .of_discrete .of_discrete]
  exact (sub_le_self _ (condEntropy_nonneg _ _ _)).trans
    (condEntropy_le_of_fiber_support μ T Z S c hS hcard)

end Disjointness.InformationTools
