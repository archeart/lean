module

public import BBCR.InternalLocalPaths
public import BBCR.LocalPublicSampler

/-! An actual zero-communication simulator for small internal information,
including exact simulation when internal information vanishes. -/

@[expose] public section

open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR.InternalSampling

open Prefix FiniteAzuma InternalPrediction

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]

noncomputable local instance : DecidableEq (X ⊕ Y) := Classical.decEq _

abbrev Public (p : Disjointness.Protocol X Y R SA SB) := R × Tape X Y p.cost p.cost

noncomputable def publicLaw (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) : PMF (Public p) :=
  joint p.publicLaw (fun r ↦ tapeLaw p μ r p.cost p.cost)

noncomputable def decodeAlice (p : Disjointness.Protocol X Y R SA SB) (x : X) (z : Public p) : p.View :=
  view p z.1 (localTrace p z.1 (.inl x) p.cost p.cost z.2 [])

noncomputable def decodeBob (p : Disjointness.Protocol X Y R SA SB) (y : Y) (z : Public p) : p.View :=
  view p z.1 (localTrace p z.1 (.inr y) p.cost p.cost z.2 [])

noncomputable def trueView (p : Disjointness.Protocol X Y R SA SB) (xy : X × Y) (z : Public p) : p.View :=
  view p z.1 (trace p z.1 xy p.cost p.cost z.2 [])

noncomputable def totalMistakes (p : Disjointness.Protocol X Y R SA SB) (xy : X × Y) (z : Public p) : ℝ :=
  mistakes p z.1 xy p.cost p.cost z.2 []

noncomputable def localSimulator (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) : Simulator p :=
  localPublicSampler p (publicLaw p μ) (decodeAlice p) (decodeBob p)

theorem localSimulator_cost (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    (localSimulator p μ).cost = 0 :=
  localPublicSampler_cost p (publicLaw p μ) (decodeAlice p) (decodeBob p)

theorem trueView_average (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (xy : X × Y) :
    (publicLaw p μ).map (trueView p xy) = p.finiteViewLaw xy.1 xy.2 := by
  rw [publicLaw,joint_eq_bind,PMF.map_bind]
  simp only [PMF.map_comp]
  have he (r : R) : (tapeLaw p μ r p.cost p.cost).map ((trueView p xy) ∘ Prod.mk r) =
      LikelihoodFrontier.conditionalViewLaw p r xy := trueView_law p μ r xy
  simp_rw [he]
  exact LikelihoodFrontier.conditionalViewLaw_average p xy

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem decoders_of_zero (p : Disjointness.Protocol X Y R SA SB) (xy : X × Y) (z : Public p)
    (hz : totalMistakes p xy z = 0) :
    decodeAlice p xy.1 z = trueView p xy z ∧ decodeBob p xy.2 z = trueView p xy z := by
  have hh := localTrace_eq_of_zero p z.1 xy p.cost p.cost z.2 [] hz
  exact ⟨congrArg (view p z.1) hh.1,congrArg (view p z.1) hh.2⟩

theorem bad_probability_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (xy : X × Y) (E : Public p → Prop) (hE : ∀ z, E z → totalMistakes p xy z ≠ 0) :
    probability (publicLaw p μ) E ≤ expect (publicLaw p μ) (totalMistakes p xy) := by
  have hm := probability_le_expect_div (publicLaw p μ) (totalMistakes p xy) 1 (by norm_num)
    (fun z _ ↦ mistakes_nonneg p z.1 xy _ _ z.2 [])
  simp only [div_one] at hm
  refine le_trans ?_ hm
  apply probability_mono
  intro z hz
  exact (mistakes_zero_or_one_le p z.1 xy _ _ z.2 []).resolve_left (hE z hz)

theorem local_fidelity_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (xy : X × Y) :
    variation (((localSimulator p μ).protocol.finiteViewLaw xy.1 xy.2).map
      ((localSimulator p μ).aliceDecode xy.1)) (p.finiteViewLaw xy.1 xy.2) ≤
      expect (publicLaw p μ) (totalMistakes p xy) := by
  rw [localSimulator,localPublicSampler_law,← trueView_average p μ xy]
  apply (variation_map_le_disagreement _ _ _).trans
  apply bad_probability_le
  intro z hz hh
  exact hz (decoders_of_zero p xy z hh).1

theorem local_agreement_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (xy : X × Y) :
    probability (publicLaw p μ) (fun z ↦ decodeAlice p xy.1 z ≠ decodeBob p xy.2 z) ≤
      expect (publicLaw p μ) (totalMistakes p xy) := by
  apply bad_probability_le
  intro z hz hh
  have he := decoders_of_zero p xy z hh
  exact hz (he.1.trans he.2.symm)

theorem average_totalMistakes (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    expect μ (fun xy ↦ expect (publicLaw p μ) (totalMistakes p xy)) = expectedDisagreement p μ := by
  have he (xy : X × Y) : expect (publicLaw p μ) (totalMistakes p xy) =
      expect p.publicLaw (fun r ↦ expect (tapeLaw p μ r p.cost p.cost)
        (fun tape ↦ mistakes p r xy p.cost p.cost tape [])) := by
    rw [publicLaw,joint_eq_bind,expect_bind]
    simp_rw [expect_map]
    rfl
  simp_rw [he]
  rw [expect_comm μ p.publicLaw (fun xy r ↦ expect (tapeLaw p μ r p.cost p.cost)
    (fun tape ↦ mistakes p r xy p.cost p.cost tape []))]
  exact average_mistakes p μ

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

theorem localSimulator_simulates (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    (localSimulator p μ).Simulates μ (Real.sqrt ((p.cost : ℝ) * internalInformation p μ)) := by
  constructor
  · apply le_trans _ (expectedDisagreement_le_sqrt p μ)
    rw [← average_totalMistakes]
    apply Finset.sum_le_sum
    intro xy _
    exact mul_le_mul_of_nonneg_left (local_fidelity_le p μ xy) (mass_nonneg μ xy)
  · apply le_trans _ (expectedDisagreement_le_sqrt p μ)
    rw [localSimulator,localPublicSampler_agreement,← average_totalMistakes]
    exact Finset.sum_le_sum fun xy _ ↦ mul_le_mul_of_nonneg_left (local_agreement_le p μ xy) (mass_nonneg μ xy)

end BBCR.InternalSampling

namespace BBCR

open InternalSampling

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

theorem small_internal_information_compression (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : 0 ≤ ε) (hinfo : (p.cost : ℝ) * internalInformation p μ ≤ ε ^ 2) :
    ∃ s : Simulator p, s.cost = 0 ∧ s.Simulates μ ε := by
  have hsqrt : Real.sqrt ((p.cost : ℝ) * internalInformation p μ) ≤ ε := by
    have hh := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg p.cost) (internalInformation_nonneg p μ))
    nlinarith [Real.sqrt_nonneg ((p.cost : ℝ) * internalInformation p μ)]
  exact ⟨localSimulator p μ,localSimulator_cost p μ,
    (localSimulator_simulates p μ).1.trans hsqrt,(localSimulator_simulates p μ).2.trans hsqrt⟩

theorem zero_internal_information_compression (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (hinfo : internalInformation p μ = 0) : ∃ s : Simulator p, s.cost = 0 ∧ s.Simulates μ 0 := by
  apply small_internal_information_compression p μ 0 (by norm_num)
  simp [hinfo]

end BBCR
