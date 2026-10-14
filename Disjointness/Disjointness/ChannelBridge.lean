module

public import Disjointness.FiniteView
public import Disjointness.BinaryInformation

/-! The finite channel description agrees with the protocol's conditional information cost. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Disjointness.Protocol

open FiniteLaw

variable {D X Y R SA SB : Type*}
  [Fintype D] [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace D] [DiscreteMeasurableSpace D]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

local instance {E F : Type*} [Finite E] (f : E → F) : FiniteRange f := ⟨Set.finite_range f⟩

def observed (p : Protocol X Y R SA SB) (s : InformationSample D X Y R SA SB) : p.View :=
  p.runView s.1.2.1 s.1.2.2 s.2

omit [MeasurableSpace D] [DiscreteMeasurableSpace D]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem executionLaw_channel (p : Protocol X Y R SA SB) (w : PMF D) (q : D → PMF (X × Y)) :
    (p.executionLaw (joint w q)).map (fun s ↦ (s.1.1, (s.1.2, p.observed s))) =
      joint w (fun d ↦ joint (q d) (fun xy ↦ p.finiteViewLaw xy.1 xy.2)) := by
  simp only [executionLaw, joint_eq_bind, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
    finiteViewLaw, Function.comp_def, observed]

/-- The public seed can move from conditioning into the observed view because it
is independent of the analysis variable and inputs. It is not charged as information. -/
theorem informationCost_eq_view (p : Protocol X Y R SA SB) (μ : PMF (D × (X × Y))) :
    p.informationCost μ = condMutualInfo (fun s : InformationSample D X Y R SA SB ↦ s.1.2)
      p.observed (fun s ↦ s.1.1) (p.executionLaw μ).toMeasure := by
  rw [informationCost, condMutualInfo_eq' .of_discrete .of_discrete .of_discrete,
    condMutualInfo_eq' .of_discrete .of_discrete .of_discrete]
  congr 1
  · exact condEntropy_prod_eq_of_indepFun
      (X := fun s : InformationSample D X Y R SA SB ↦ s.1.2)
      (Y := fun s ↦ s.1.1) (Z := fun s ↦ s.2.1)
      .of_discrete .of_discrete .of_discrete
      ((p.executionLaw_indep μ).comp
        (show Measurable (fun s : D × (X × Y) ↦ (s.2, s.1)) from .of_discrete)
        (show Measurable (Prod.fst : R × (SA × SB) → R) from .of_discrete))
  · let f : p.View × D → List Bool × (D × R) := fun v ↦ (v.1.2.1, (v.2, v.1.1))
    have hf : Function.Injective f := by
      rintro ⟨v,d⟩ ⟨v',d'⟩ h
      have hv : v = v' := p.forgetView_injective (by
        exact Prod.ext (congrArg (fun z ↦ z.2.2) h) (congrArg Prod.fst h))
      exact Prod.ext hv (congrArg (fun z ↦ z.2.1) h)
    exact condEntropy_of_injective' (p.executionLaw μ).toMeasure
      (show Measurable (fun s : InformationSample D X Y R SA SB ↦ s.1.2) from .of_discrete)
      (show Measurable (fun s : InformationSample D X Y R SA SB ↦ (p.observed s, s.1.1)) from .of_discrete)
      f hf .of_discrete

/-- A computational finite-channel formula for the exact protocol information cost. -/
theorem informationCost_eq_channel (p : Protocol X Y R SA SB)
    (w : PMF D) (q : D → PMF (X × Y)) :
    p.informationCost (joint w q) = Channel.conditional w q (fun xy ↦ p.finiteViewLaw xy.1 xy.2) := by
  rw [informationCost_eq_view, Channel.conditional_eq_condMutualInfo]
  apply InformationTools.condMutualInfo_identDistrib
  refine ⟨.of_discrete, .of_discrete, ?_⟩
  rw [← p.executionLaw_channel w q, ← PMF.toMeasure_map _ _ .of_discrete,
    Measure.map_map .of_discrete .of_discrete]
  rfl

end Disjointness.Protocol
