module

public import BBCR.PrefixAccounting
public import BBCR.Simulation

/-! Disintegration over the independent public seed, for arbitrary finite input
and analysis distributions. The resulting divergence expectation is the actual
external information from the simulation interface. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger
open scoped Classical

namespace BBCR

variable {D X Y R SA SB : Type} [Fintype D] [Fintype X] [Fintype Y]
  [Fintype R] [Fintype SA] [Fintype SB]

noncomputable def groupedExecution (p : Protocol X Y R SA SB) (w : PMF D)
    (q : D → PMF (X × Y)) : PMF ((D × R) × Prefix.Prior.Sample X Y SA SB) :=
  joint (joint w (fun _ ↦ p.publicLaw)) (fun dr ↦ Prefix.Prior.execution p (q dr.1))

theorem execution_regroup (p : Protocol X Y R SA SB) (w : PMF D) (q : D → PMF (X × Y)) :
    (p.executionLaw (joint w q)).map Protocol.regroup = groupedExecution p w q := by
  apply PMF.ext
  rintro ⟨⟨d,r⟩,xy,a,b⟩
  rw [map_equiv_apply]
  simp only [Protocol.regroup, Equiv.coe_fn_symm_mk, Protocol.executionLaw, joint_apply,
    Protocol.seedLaw_apply, groupedExecution, Prefix.Prior.execution, Prefix.Experiment.privateSeeds]
  ring

theorem execution_conditioning (p : Protocol X Y R SA SB) (w : PMF D) (q : D → PMF (X × Y)) :
    (p.executionLaw (joint w q)).map Protocol.conditioning = joint w (fun _ ↦ p.publicLaw) := by
  have hh := congrArg (fun law ↦ law.map Prod.fst) (execution_regroup p w q)
  rw [groupedExecution, joint_map_fst, PMF.map_comp] at hh
  change (p.executionLaw (joint w q)).map Protocol.conditioning = _ at hh
  exact hh

variable [MeasurableSpace D] [DiscreteMeasurableSpace D]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

local instance publicInformationFiniteRange {E F : Type*} [Finite E] (f : E → F) : FiniteRange f :=
  ⟨Set.finite_range f⟩

theorem execution_conditioning_mass (p : Protocol X Y R SA SB) (w : PMF D)
    (q : D → PMF (X × Y)) (dr : D × R) :
    (p.executionLaw (joint w q)).toMeasure (Protocol.conditioning ⁻¹' {dr}) =
      joint w (fun _ ↦ p.publicLaw) dr := by
  rw [FiniteCondition.fiber_measure, execution_conditioning]

theorem information_conditioned_public (p : Protocol X Y R SA SB) (w : PMF D)
    (q : D → PMF (X × Y)) (dr : D × R) (hpos : joint w (fun _ ↦ p.publicLaw) dr ≠ 0) :
    mutualInfo (fun s ↦ s.1.2) p.communicated
      ((p.executionLaw (joint w q)).toMeasure[|Protocol.conditioning ⁻¹' {dr}]) =
      mutualInfo Prod.fst
        (fun ω ↦ Prefix.Experiment.transcript p dr.2 ω.1.1 ω.1.2 ω.2)
        (Prefix.Prior.execution p (q dr.1)).toMeasure := by
  let ν := (p.executionLaw (joint w q)).toMeasure
  have hreg : ν.map Protocol.regroup = (groupedExecution p w q).toMeasure := by
    rw [PMF.toMeasure_map _ _ .of_discrete, execution_regroup]
  have hc := map_cond_preimage ν (show Measurable Protocol.regroup from .of_discrete)
    (show MeasurableSet (Prod.fst ⁻¹' {dr}) from .of_discrete)
  rw [hreg, groupedExecution, joint_cond_fst _ _ _ hpos] at hc
  let observe : (D × R) × Prefix.Prior.Sample X Y SA SB → (X × Y) × List Bool :=
    fun z ↦ (z.2.1, Prefix.Experiment.transcript p z.1.2 z.2.1.1 z.2.1.2 z.2.2)
  have hm := congrArg (fun law ↦ law.map observe) hc
  rw [Measure.map_map (show Measurable observe from .of_discrete)
    (show Measurable Protocol.regroup from .of_discrete),
    PMF.toMeasure_map _ _ (show Measurable observe from .of_discrete)] at hm
  have hpmf : (joint (PMF.pure dr) (fun _ ↦ Prefix.Prior.execution p (q dr.1))).map observe =
      (Prefix.Prior.execution p (q dr.1)).map (fun ω ↦
        (ω.1, Prefix.Experiment.transcript p dr.2 ω.1.1 ω.1.2 ω.2)) := by
    simp only [joint_eq_bind, PMF.pure_bind, PMF.map_comp, Function.comp_def, observe]
  rw [hpmf, ← PMF.toMeasure_map _ _ (.of_discrete)] at hm
  apply IdentDistrib.mutualInfo_eq
  exact ⟨.of_discrete, .of_discrete, hm⟩

/-- Conditional external information is an average of actual fixed-public-seed
experiments. This applies to any correlated input prior, not just DISJ's law. -/
theorem informationCost_eq_public_average (p : Protocol X Y R SA SB) (w : PMF D)
    (q : D → PMF (X × Y)) :
    p.informationCost (joint w q) = ∑ dr : D × R,
      mass (joint w (fun _ ↦ p.publicLaw)) dr *
        mutualInfo Prod.fst (fun ω ↦ Prefix.Experiment.transcript p dr.2 ω.1.1 ω.1.2 ω.2)
          (Prefix.Prior.execution p (q dr.1)).toMeasure := by
  rw [Protocol.informationCost_eq_sum]
  apply Finset.sum_congr rfl
  intro dr _
  rw [measureReal_def, execution_conditioning_mass]
  by_cases h : joint w (fun _ ↦ p.publicLaw) dr = 0
  · simp [h, mass]
  · rw [information_conditioned_public p w q dr h]
    rfl

omit [Fintype D] [MeasurableSpace D] [DiscreteMeasurableSpace D] in
theorem externalInformation_eq_public_average (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    externalInformation p μ = ∑ r, mass p.publicLaw r *
      mutualInfo Prod.fst (fun ω ↦ Prefix.Experiment.transcript p r ω.1.1 ω.1.2 ω.2)
        (Prefix.Prior.execution p μ).toMeasure := by
  rw [externalInformation_eq_conditional, informationCost_eq_public_average]
  simp [Fintype.sum_prod_type, mass]

omit [Fintype D] [MeasurableSpace D] [DiscreteMeasurableSpace D] in
/-- Expected accumulated Alice/Bob KL costs equal external information, with
both the actual private execution and independent public seed averaged out. -/
theorem expected_divergence_eq_externalInformation (p : Protocol X Y R SA SB)
    (μ : PMF (X × Y)) :
    (∑ r, mass p.publicLaw r * ∑ ω, mass (Prefix.Prior.execution p μ) ω *
      Prefix.Prior.pathDivergence p μ r p.cost ω) = externalInformation p μ := by
  rw [externalInformation_eq_public_average]
  apply Finset.sum_congr rfl
  intro r _
  rw [Prefix.Prior.expected_full_divergence p μ r p.cost (p.depth_le_cost r)]

end BBCR
