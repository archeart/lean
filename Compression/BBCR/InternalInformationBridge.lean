module

public import BBCR.InternalInformation

/-! The conditional-prior definition of internal information is the usual
I(X;view|Y) + I(Y;view|X), with the original public seed included in the view. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR

section ConditionalInput

variable {A B H : Type} [Fintype A] [Fintype B] [Fintype H]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [MeasurableSpace B] [DiscreteMeasurableSpace B]
  [MeasurableSpace H] [DiscreteMeasurableSpace H]

/-- Conditional information is the average information of the actual input
law on each coordinate fiber. -/
theorem conditional_input_information (μ : PMF A) (f : A → H) (K : A → PMF B) :
    (∑ h, mass (μ.map f) h * Disjointness.Channel.information (FiniteCondition.law μ f h) K) =
      condMutualInfo Prod.fst Prod.snd (fun z : A × B ↦ f z.1) (joint μ K).toMeasure := by
  change conditionalInformation (μ.map f) (FiniteCondition.law μ f) (fun _ ↦ K) = _
  rw [conditionalInformation_eq_condMutualInfo]
  apply Disjointness.InformationTools.condMutualInfo_identDistrib
  refine ⟨.of_discrete,.of_discrete,?_⟩
  rw [PMF.toMeasure_map _ _ (.of_discrete), PMF.toMeasure_map _ _ (.of_discrete)]
  congr 1
  rw [FiniteCondition.joint_condition, PMF.map_comp]
  rfl

end ConditionalInput

section KnownCoordinate

variable {Ω X Y T : Type} [Fintype Ω] [Fintype X] [Fintype Y] [Fintype T]
  [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace T] [DiscreteMeasurableSpace T]

local instance finiteRange {A B : Type} [Finite A] (f : A → B) : FiniteRange f := ⟨Set.finite_range f⟩

theorem cond_information_pair_snd (ν : Measure Ω) [IsProbabilityMeasure ν]
    (x : Ω → X) (y : Ω → Y) (t : Ω → T) :
    condMutualInfo (fun ω ↦ (x ω,y ω)) t y ν = condMutualInfo x t y ν := by
  rw [condMutualInfo_comm (X := fun ω ↦ (x ω,y ω)) (Y := t) (.of_discrete) (.of_discrete),
    condMutualInfo_comm (X := x) (Y := t) (.of_discrete) (.of_discrete)]
  rw [condMutualInfo_eq' (.of_discrete) (.of_discrete) (.of_discrete),
    condMutualInfo_eq' (.of_discrete) (.of_discrete) (.of_discrete)]
  have hh := condEntropy_of_injective' ν (show Measurable t from .of_discrete)
    (show Measurable (fun ω ↦ (x ω,y ω)) from .of_discrete)
    (fun z : X × Y ↦ (z,z.2)) (fun _ _ h ↦ congrArg Prod.fst h) (.of_discrete)
  exact congrArg (fun z ↦ condEntropy t y ν - z) hh

theorem cond_information_pair_fst (ν : Measure Ω) [IsProbabilityMeasure ν]
    (x : Ω → X) (y : Ω → Y) (t : Ω → T) :
    condMutualInfo (fun ω ↦ (x ω,y ω)) t x ν = condMutualInfo y t x ν := by
  have hswap := condEntropy_of_injective' ν (show Measurable t from .of_discrete)
    (show Measurable (fun ω ↦ (y ω,x ω)) from .of_discrete)
    (fun z : Y × X ↦ ((z.2,z.1),z.2)) (by intro a b h; cases a; cases b; simp_all) (.of_discrete)
  rw [condMutualInfo_comm (X := fun ω ↦ (x ω,y ω)) (Y := t) (.of_discrete) (.of_discrete),
    condMutualInfo_comm (X := y) (Y := t) (.of_discrete) (.of_discrete)]
  rw [condMutualInfo_eq' (.of_discrete) (.of_discrete) (.of_discrete),
    condMutualInfo_eq' (.of_discrete) (.of_discrete) (.of_discrete)]
  exact congrArg (fun z ↦ condEntropy t x ν - z) hswap

end KnownCoordinate

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

omit [Fintype SA] [Fintype SB] [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA] [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem internalInformation_eq_condMutualInfo (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    internalInformation p μ =
      condMutualInfo (fun z : (X × Y) × p.View ↦ z.1.1) Prod.snd (fun z ↦ z.1.2)
        (joint μ (fun xy ↦ p.finiteViewLaw xy.1 xy.2)).toMeasure +
      condMutualInfo (fun z : (X × Y) × p.View ↦ z.1.2) Prod.snd (fun z ↦ z.1.1)
        (joint μ (fun xy ↦ p.finiteViewLaw xy.1 xy.2)).toMeasure := by
  unfold internalInformation externalInformation alicePrior bobPrior
  rw [conditional_input_information, conditional_input_information]
  let ν := (joint μ (fun xy ↦ p.finiteViewLaw xy.1 xy.2)).toMeasure
  have ha := cond_information_pair_fst ν (fun z : (X × Y) × p.View ↦ z.1.1) (fun z ↦ z.1.2) Prod.snd
  have hb := cond_information_pair_snd ν (fun z : (X × Y) × p.View ↦ z.1.1) (fun z ↦ z.1.2) Prod.snd
  exact (congrArg₂ (· + ·) ha hb).trans (add_comm _ _)

end BBCR
