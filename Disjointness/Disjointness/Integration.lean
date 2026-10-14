module

public import PFR.ForMathlib.Entropy.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Dependency integration

Small checked interfaces for the BJKS project. These are library integration
results, not a protocol information bound or a DISJ lower bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Disjointness.Integration

section Finite

variable {Ω A B C : Type*}
  [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [Fintype B] [MeasurableSpace B] [DiscreteMeasurableSpace B]
  [Fintype C] [MeasurableSpace C] [DiscreteMeasurableSpace C]

/-- A finite PMF can be used directly with PFR's entropy chain rule. -/
theorem pmf_chain_rule (p : PMF Ω) (X : Ω → A) (Y : Ω → B) :
    entropy (fun ω ↦ (X ω, Y ω)) p.toMeasure =
      entropy Y p.toMeasure + condEntropy X Y p.toMeasure := by
  exact chain_rule p.toMeasure (.of_discrete) (.of_discrete)

omit [Fintype C] [DiscreteMeasurableSpace C] in
/-- PFR's conditional information is nonnegative on finite PMF models. -/
theorem pmf_condMutualInfo_nonneg (p : PMF Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    0 ≤ condMutualInfo X Y Z p.toMeasure := by
  exact condMutualInfo_nonneg (.of_discrete) (.of_discrete)

/-- The communication-bound interface: conditional information is bounded by
the logarithm of the transcript alphabet. A protocol support bound is still needed. -/
theorem pmf_condMutualInfo_le_log_card (p : PMF Ω)
    (X : Ω → A) (T : Ω → B) (Z : Ω → C) :
    condMutualInfo X T Z p.toMeasure ≤ Real.log (Fintype.card B) := by
  rw [condMutualInfo_comm (.of_discrete) (.of_discrete) Z p.toMeasure,
    condMutualInfo_eq' (.of_discrete) (.of_discrete) (.of_discrete)]
  exact (sub_le_self _ (condEntropy_nonneg _ _ _)).trans
    (condEntropy_le_log_card T Z p.toMeasure)

omit [Fintype A] [DiscreteMeasurableSpace A] [Fintype B] [DiscreteMeasurableSpace B] in
/-- Conditioning can be expanded into a finite weighted sum, including values
of the conditioning variable with probability zero. -/
theorem pmf_condMutualInfo_eq_sum (p : PMF Ω)
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    condMutualInfo X Y Z p.toMeasure =
      ∑ z, p.toMeasure.real (Z ⁻¹' {z}) *
        mutualInfo X Y (p.toMeasure[|Z ⁻¹' {z}]) := by
  exact condMutualInfo_eq_sum' (.of_discrete)

/-- Two-variable conditional subadditivity, obtained from PFR information
nonnegativity. This is an interface needed for coordinate decomposition. -/
theorem pmf_condEntropy_pair_le (p : PMF Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    condEntropy (fun ω ↦ (X ω, Y ω)) Z p.toMeasure ≤
      condEntropy X Z p.toMeasure + condEntropy Y Z p.toMeasure := by
  have h := pmf_condMutualInfo_nonneg p X Y Z
  rw [condMutualInfo_eq (.of_discrete) (.of_discrete) (.of_discrete)] at h
  exact sub_nonneg.mp h

end Finite

/-- Fixed-length binary transcripts give the correct natural-log-to-bit factor.
Variable-length protocol transcripts still require a proved encoding/support lemma. -/
theorem pmf_condMutualInfo_bitvec_le {Ω A C : Type*}
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    [Fintype C] [MeasurableSpace C] [DiscreteMeasurableSpace C]
    (p : PMF Ω) (c : ℕ) (X : Ω → A) (T : Ω → (Fin c → Bool)) (Z : Ω → C) :
    condMutualInfo X T Z p.toMeasure ≤ (c : ℝ) * Real.log 2 := by
  simpa [Fintype.card_fun, Real.log_pow] using pmf_condMutualInfo_le_log_card p X T Z

/-- Mathlib's extended-valued KL distinguishes finite PMFs exactly. This does not
yet connect KL to PFR mutual information or to Hellinger distance. -/
theorem pmf_klDiv_eq_zero_iff {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (p q : PMF Ω) :
    InformationTheory.klDiv p.toMeasure q.toMeasure = 0 ↔ p = q := by
  rw [InformationTheory.klDiv_eq_zero_iff, PMF.toMeasure_inj]

end Disjointness.Integration
