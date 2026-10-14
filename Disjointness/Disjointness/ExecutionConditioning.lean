module

public import Disjointness.InformationCost

/-! The input law after conditioning on both the switch and the public seed. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Disjointness.Protocol

open FiniteLaw

variable {X Y R SA SB : Type*} [Fintype R] [Fintype SA] [Fintype SB]

theorem seedLaw_eq_joint (p : Protocol X Y R SA SB) :
    p.seedLaw = joint p.publicLaw (fun _ ↦ joint p.aliceLaw (fun _ ↦ p.bobLaw)) := by
  simp [seedLaw, joint_eq_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem seedLaw_apply (p : Protocol X Y R SA SB) (r : R) (a : SA) (b : SB) :
    p.seedLaw (r, (a, b)) = p.publicLaw r * (p.aliceLaw a * p.bobLaw b) := by
  rw [seedLaw_eq_joint, joint_apply, joint_apply]

/-- Regroup the sample as `((D,R),((X,Y),(SA,SB)))`. -/
def regroup {D : Type*} : InformationSample D X Y R SA SB ≃
    (D × R) × ((X × Y) × (SA × SB)) where
  toFun s := ((s.1.1, s.2.1), (s.1.2, s.2.2))
  invFun s := ((s.1.1, s.2.1), (s.1.2, s.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def groupedLaw {n : ℕ} (p : Protocol (Bits n) (Bits n) R SA SB) :
    PMF ((Bits n × R) × ((Bits n × Bits n) × (SA × SB))) :=
  joint (joint (Switch.switches n) (fun _ ↦ p.publicLaw))
    (fun dr ↦ joint (Switch.inputLaw dr.1) (fun _ ↦ joint p.aliceLaw (fun _ ↦ p.bobLaw)))

theorem executionLaw_regroup {n : ℕ} (p : Protocol (Bits n) (Bits n) R SA SB) :
    (p.executionLaw (Switch.law n)).map regroup = p.groupedLaw := by
  ext ⟨⟨d, r⟩, xy, a, b⟩
  rw [map_equiv_apply]
  simp only [regroup, Equiv.coe_fn_symm_mk, executionLaw, joint_apply, Switch.law,
    seedLaw_apply, groupedLaw]
  ring

variable [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

/-- The joint law of the switches and public seed is their independent product. -/
theorem executionLaw_conditioning {n : ℕ} (p : Protocol (Bits n) (Bits n) R SA SB) :
    (p.executionLaw (Switch.law n)).toMeasure.map conditioning =
      (joint (Switch.switches n) (fun _ ↦ p.publicLaw)).toMeasure := by
  have h := congrArg (fun q ↦ q.map Prod.fst) p.executionLaw_regroup
  rw [groupedLaw, joint_map_fst, PMF.map_comp] at h
  change (p.executionLaw (Switch.law n)).map conditioning = _ at h
  rw [PMF.toMeasure_map _ _ .of_discrete, h]

/-- Positive public-seed fibers retain exactly the intended conditional input law.
In particular, revealing the public seed does not reveal additional input information. -/
theorem conditional_inputLaw {n : ℕ} (p : Protocol (Bits n) (Bits n) R SA SB)
    (d : Bits n) (r : R) (hr : p.publicLaw r ≠ 0) :
    ((p.executionLaw (Switch.law n)).toMeasure[|conditioning ⁻¹' {(d, r)}]).map
      (fun s ↦ s.1.2) = (Switch.inputLaw d).toMeasure := by
  let μ := (p.executionLaw (Switch.law n)).toMeasure
  have hg : μ.map regroup = p.groupedLaw.toMeasure := by
    rw [PMF.toMeasure_map _ _ .of_discrete, executionLaw_regroup]
  have hc := map_cond_preimage μ (show Measurable regroup from .of_discrete)
    (show MeasurableSet (Prod.fst ⁻¹' {(d, r)}) from .of_discrete)
  rw [hg, groupedLaw, joint_cond_fst _ _ _ (mul_ne_zero (Switch.switches_pos d) hr),
    joint_const_toMeasure, joint_const_toMeasure] at hc
  have hm := congrArg (fun ν ↦ ν.map (fun s ↦ s.2.1)) hc
  rw [Measure.map_map (show Measurable (fun s :
      (Bits n × R) × ((Bits n × Bits n) × (SA × SB)) ↦ s.2.1) from .of_discrete)
      (show Measurable regroup from .of_discrete)] at hm
  change (μ[|conditioning ⁻¹' {(d, r)}]).map (fun s ↦ s.1.2) =
    ((PMF.pure (d, r)).toMeasure.prod ((Switch.inputLaw d).toMeasure.prod
      (joint p.aliceLaw (fun _ ↦ p.bobLaw)).toMeasure)).map (Prod.fst ∘ Prod.snd) at hm
  rw [← Measure.map_map measurable_fst measurable_snd, Measure.map_snd_prod,
    measure_univ, one_smul, Measure.map_fst_prod, measure_univ, one_smul] at hm
  exact hm

theorem conditioning_fiber {n : ℕ} (p : Protocol (Bits n) (Bits n) R SA SB)
    (d : Bits n) (r : R) :
    (p.executionLaw (Switch.law n)).toMeasure (conditioning ⁻¹' {(d, r)}) =
      Switch.switches n d * p.publicLaw r := by
  rw [← Measure.map_apply (show Measurable conditioning from .of_discrete) (.singleton _),
    executionLaw_conditioning, PMF.toMeasure_apply_singleton _ _ (.singleton _), joint_apply]

/-- A zero-mass public seed gives the zero conditional measure, not an arbitrary law. -/
theorem conditional_zero_of_publicLaw_zero {n : ℕ}
    (p : Protocol (Bits n) (Bits n) R SA SB) (d : Bits n) (r : R) (hr : p.publicLaw r = 0) :
    (p.executionLaw (Switch.law n)).toMeasure[|conditioning ⁻¹' {(d, r)}] = 0 := by
  apply cond_eq_zero_of_meas_eq_zero
  rw [conditioning_fiber, hr, mul_zero]

/-- Coordinate independence holds under the actual conditioning used in `J`. -/
theorem bjks_coordinates_condIndep {n : ℕ} (p : Protocol (Bits n) (Bits n) R SA SB)
    (d : Bits n) (r : R) (hr : p.publicLaw r ≠ 0) :
    iIndepFun (fun i s ↦ (s.1.2.1 i, s.1.2.2 i))
      ((p.executionLaw (Switch.law n)).toMeasure[|conditioning ⁻¹' {(d, r)}]) := by
  have : IsProbabilityMeasure
      ((p.executionLaw (Switch.law n)).toMeasure[|conditioning ⁻¹' {(d, r)}]) :=
    cond_isProbabilityMeasure_of_finite (by
      rw [conditioning_fiber]
      exact mul_ne_zero (Switch.switches_pos d) hr) (measure_ne_top _ _)
  exact iIndep_pullback (show Measurable (fun s :
      InformationSample (Bits n) (Bits n) (Bits n) R SA SB ↦ s.1.2) from .of_discrete)
    (p.conditional_inputLaw d r hr) (fun _ ↦ .of_discrete) (Switch.inputLaw_iIndep d)

/-- The two complete inputs are independent given the switches and public seed. -/
theorem bjks_players_condIndep {n : ℕ} (p : Protocol (Bits n) (Bits n) R SA SB) :
    CondIndepFun (fun s ↦ s.1.2.1) (fun s ↦ s.1.2.2) conditioning
      (p.executionLaw (Switch.law n)).toMeasure := by
  apply Filter.Eventually.of_forall
  rintro ⟨d, r⟩
  by_cases hr : p.publicLaw r = 0
  · rw [conditional_zero_of_publicLaw_zero p d r hr]
    exact indepFun_zero_measure
  · have : IsProbabilityMeasure
        ((p.executionLaw (Switch.law n)).toMeasure[|conditioning ⁻¹' {(d, r)}]) :=
      cond_isProbabilityMeasure_of_finite (by
        rw [conditioning_fiber]
        exact mul_ne_zero (Switch.switches_pos d) hr) (measure_ne_top _ _)
    exact indep_pullback (show Measurable (fun s :
        InformationSample (Bits n) (Bits n) (Bits n) R SA SB ↦ s.1.2) from .of_discrete)
      (p.conditional_inputLaw d r hr) measurable_fst measurable_snd (Switch.inputLaw_indep d)

end Disjointness.Protocol
