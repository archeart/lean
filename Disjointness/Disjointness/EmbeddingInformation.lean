module

public import Disjointness.Embedding

/-! Exact distribution and information identities for the coordinate embeddings. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Disjointness

open FiniteLaw Hellinger Channel

namespace Switch

noncomputable def bitInput (b : Bool) : PMF (Bool × Bool) :=
  joint (bitLaw b) (fun _ ↦ bitLaw (!b))

/-- Replacing the selected coordinate by a fresh switch-conditioned pair gives
exactly the original product input law with that switch replaced. -/
theorem inputLaw_fill {n : ℕ} (i : Fin n) (d : Bits n) (b : Bool) :
    (joint (bitInput b) (fun _ ↦ inputLaw d)).map (fun z ↦ fill i z.1 z.2) =
      inputLaw (Function.update d i b) := by
  apply map_equiv_injective (coordinatesEquiv n)
  rw [PMF.map_comp, inputLaw_map_coordinates]
  have hm := joint_map_second (bitInput b) (fun _ ↦ inputLaw d) (coordinatesEquiv n)
  simp_rw [inputLaw_map_coordinates] at hm
  have hr := congrArg (fun p ↦ p.map (fun z ↦ Function.update z.2 i z.1)) hm
  rw [PMF.map_comp, pi_replace] at hr
  have hf : (coordinatesEquiv n) ∘ (fun z : (Bool × Bool) × (Bits n × Bits n) ↦ fill i z.1 z.2) =
      (fun z : (Bool × Bool) × (Fin n → Bool × Bool) ↦ Function.update z.2 i z.1) ∘
        (fun z ↦ (z.1, coordinatesEquiv n z.2)) := by
    funext z j
    by_cases hj : j = i
    · subst j
      simp [fill, coordinatesEquiv]
    · simp [fill, coordinatesEquiv, Function.update_of_ne hj]
  rw [hf, hr]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp [bitInput]
  · simp [Function.update_of_ne hj]

/-- The selected input pair and the observed channel output have the exact same
joint law in the embedding and the original coordinate experiment. -/
theorem joint_fill_channel {n : ℕ} {V : Type*} [Fintype V]
    (i : Fin n) (d : Bits n) (b : Bool) (K : (Bits n × Bits n) → PMF V) :
    joint (bitInput b) (fun xy ↦ (inputLaw d).bind (fun z ↦ K (fill i xy z))) =
      (joint (inputLaw (Function.update d i b)) K).map (fun z ↦ ((z.1.1 i, z.1.2 i), z.2)) := by
  rw [← inputLaw_fill i d b]
  simp only [joint_eq_bind, PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.map_comp,
    Function.comp_def, fill, Function.update_self]

end Switch

namespace Protocol

variable {n : ℕ} {R SA SB : Type*} [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

omit [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem embed_branch_information (p : Protocol (Bits n) (Bits n) R SA SB)
    (i : Fin n) (d : Bits n) (b : Bool) :
    information (Switch.bitInput b) (fun xy ↦ (p.embed i d).finiteViewLaw xy.1 xy.2) =
      p.coordinateInformation i (Function.update d i b) := by
  let e : (p.embed i d).View ≃ p.View := p.randomViewEquiv (Switch.aliceLaw d) (Switch.bobLaw d)
    (fun x a ↦ Function.update a i x) (fun y a ↦ Function.update a i y) Bool.not
  have he := information_map_output (Switch.bitInput b)
    (fun xy : Bool × Bool ↦ (p.embed i d).finiteViewLaw xy.1 xy.2) e e.injective
  rw [← he]
  have hv (xy : Bool × Bool) : ((p.embed i d).finiteViewLaw xy.1 xy.2).map e =
      (Switch.inputLaw d).bind (fun z ↦ p.finiteViewLaw (Switch.fill i xy z).1 (Switch.fill i xy z).2) :=
    p.localRandomize_viewLaw _ _ _ _ _ _ _
  simp_rw [hv]
  unfold information coordinateInformation
  apply IdentDistrib.mutualInfo_eq
  refine ⟨.of_discrete, .of_discrete, ?_⟩
  change (joint (Switch.bitInput b) (fun xy ↦ (Switch.inputLaw d).bind
    (fun z ↦ p.finiteViewLaw (Switch.fill i xy z).1 (Switch.fill i xy z).2))).toMeasure.map id = _
  rw [Measure.map_id, PMF.toMeasure_map _ _ .of_discrete,
    Switch.joint_fill_channel i d b (fun xy ↦ p.finiteViewLaw xy.1 xy.2)]

/-- Each embedded AND information cost is the average of the two possible
selected-switch coordinate terms, with all other switches held fixed. -/
theorem embed_informationCost (p : Protocol (Bits n) (Bits n) R SA SB)
    (i : Fin n) (d : Bits n) :
    (p.embed i d).andInformationCost =
      (p.coordinateInformation i (Function.update d i false) +
        p.coordinateInformation i (Function.update d i true)) / 2 := by
  rw [andInformationCost, Switch.coordinateLaw, informationCost_eq_channel]
  change (∑ b, mass Switch.fair b * information (Switch.bitInput b)
    (fun xy ↦ (p.embed i d).finiteViewLaw xy.1 xy.2)) = _
  simp_rw [embed_branch_information, fair_mass]
  simp only [Fintype.sum_bool]
  ring

end Protocol
end Disjointness
