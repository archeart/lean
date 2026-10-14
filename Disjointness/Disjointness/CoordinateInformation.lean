module

public import Disjointness.ChannelBridge

/-! Entropy subadditivity and the coordinate information inequality. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Disjointness.InformationTools

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
  [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [MeasurableSpace B] [DiscreteMeasurableSpace B]

/-- Conditional entropy is subadditive across any finite vector. -/
theorem condEntropy_vector_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → A) (T : Ω → B) :
    condEntropy (fun ω i ↦ X i ω) T μ ≤ ∑ i, condEntropy (X i) T μ := by
  induction n with
  | zero =>
    have h : (fun ω i ↦ X i ω) = (fun _ : Ω ↦ (Fin.elim0 : Fin 0 → A)) := by
      funext ω i
      exact Fin.elim0 i
    rw [h]
    exact (condEntropy_le_entropy (μ := μ) measurable_const .of_discrete).trans (by simp [entropy_const])
  | succ n ih =>
    let f : (Fin (n + 1) → A) → (Fin n → A) × A :=
      fun x ↦ (fun i ↦ x i.castSucc, x (Fin.last n))
    have hf : Function.Injective f := by
      intro x y h
      ext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact congrFun (congrArg Prod.fst h) j
      · exact congrArg Prod.snd h
    have he := condEntropy_of_injective μ
      (show Measurable (fun ω i ↦ X i ω) from .of_discrete)
      (show Measurable T from .of_discrete) (fun _ ↦ f) (fun _ ↦ hf)
    change condEntropy (fun ω ↦ (fun i : Fin n ↦ X i.castSucc ω, X (Fin.last n) ω)) T μ = _ at he
    rw [← he, Fin.sum_univ_castSucc]
    exact (cond_pair_le μ _ _ T).trans (add_le_add (ih _) le_rfl)

/-- Independent input coordinates force information to dominate their sum. -/
theorem sum_mutualInfo_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → A) (T : Ω → B) (h : iIndepFun X μ) :
    (∑ i, mutualInfo (X i) T μ) ≤ mutualInfo (fun ω i ↦ X i ω) T μ := by
  let : MeasureSpace Ω := ⟨μ⟩
  have he : entropy (fun ω i ↦ X i ω) μ = ∑ i, entropy (X i) μ :=
    iIndepFun.entropy_eq_add (fun _ ↦ .of_discrete) h
  simp_rw [mutualInfo_eq_entropy_sub_condEntropy (μ := μ)
    (show Measurable (X _) from .of_discrete) (show Measurable T from .of_discrete)]
  rw [mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete, he,
    Finset.sum_sub_distrib]
  exact sub_le_sub_left (condEntropy_vector_le μ X T) _

end Disjointness.InformationTools

namespace Disjointness.Protocol

open FiniteLaw Hellinger Channel

variable {n : ℕ} {R SA SB : Type*}
  [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

noncomputable def coordinateInformation (p : Protocol (Bits n) (Bits n) R SA SB)
    (i : Fin n) (d : Bits n) : ℝ :=
  mutualInfo (fun z : (Bits n × Bits n) × p.View ↦ (z.1.1 i, z.1.2 i)) Prod.snd
    (joint (Switch.inputLaw d) (fun xy ↦ p.finiteViewLaw xy.1 xy.2)).toMeasure

omit [Fintype SA] [Fintype SB] [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem sum_coordinateInformation_le (p : Protocol (Bits n) (Bits n) R SA SB) (d : Bits n) :
    ∑ i, p.coordinateInformation i d ≤
      information (Switch.inputLaw d) (fun xy ↦ p.finiteViewLaw xy.1 xy.2) := by
  let ν := (joint (Switch.inputLaw d) (fun xy ↦ p.finiteViewLaw xy.1 xy.2)).toMeasure
  have hm : ν.map Prod.fst = (Switch.inputLaw d).toMeasure := by
    rw [PMF.toMeasure_map _ _ measurable_fst, joint_map_fst]
  have hi := iIndep_pullback measurable_fst hm (fun _ ↦ .of_discrete)
    (Switch.inputLaw_iIndep d)
  have h := InformationTools.sum_mutualInfo_le ν
    (fun i z ↦ (z.1.1 i, z.1.2 i)) Prod.snd hi
  change _ ≤ mutualInfo ((Switch.coordinatesEquiv n) ∘ Prod.fst) Prod.snd ν at h
  have he : mutualInfo ((Switch.coordinatesEquiv n) ∘ Prod.fst) Prod.snd ν =
      mutualInfo Prod.fst Prod.snd ν := by
    have : FiniteRange (Prod.snd : (Bits n × Bits n) × p.View → p.View) := ⟨Set.finite_range _⟩
    have : FiniteRange (Prod.fst : (Bits n × Bits n) × p.View → Bits n × Bits n) := ⟨Set.finite_range _⟩
    rw [mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete,
      mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete,
      entropy_comp_of_injective ν measurable_fst (Switch.coordinatesEquiv n)
        (Switch.coordinatesEquiv n).injective]
    congr 1
    exact condEntropy_of_injective ν measurable_fst measurable_snd
      (fun _ ↦ Switch.coordinatesEquiv n) (fun _ ↦ (Switch.coordinatesEquiv n).injective)
  rw [he] at h
  exact h

theorem bjksInformationCost_ge_sum_coordinates (p : Protocol (Bits n) (Bits n) R SA SB) :
    (∑ i, ∑ d, mass (Switch.switches n) d * p.coordinateInformation i d) ≤
      p.bjksInformationCost := by
  rw [bjksInformationCost, Switch.law, informationCost_eq_channel, conditional, Finset.sum_comm]
  exact Finset.sum_le_sum (fun d _ ↦ by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (p.sum_coordinateInformation_le d) (mass_nonneg _ _))

end Disjointness.Protocol
