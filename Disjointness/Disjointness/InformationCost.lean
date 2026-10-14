module

public import Disjointness.InformationTools
public import Disjointness.Switch
public import Disjointness.Factorization

/-!
# Protocol conditional information cost

`Protocol.informationCost p μ` is `I((X,Y);T | (D,R))` under the joint
input/analysis law `μ`, independently sampled public and private protocol seeds,
and the actual tree execution. Entropies are in nats. The analysis variable `D`
does not enter execution. The public seed is conditioned on, not charged.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Disjointness.Protocol

instance transcriptMeasurableSpace : MeasurableSpace (List Bool) := ⊤
instance transcriptDiscreteMeasurableSpace : DiscreteMeasurableSpace (List Bool) := ⟨fun _ ↦ trivial⟩

variable {D X Y R SA SB : Type*}
  [Fintype D] [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]

abbrev InformationSample (D X Y R SA SB : Type*) := (D × (X × Y)) × (R × (SA × SB))

/-- Inputs and the analysis variable are sampled independently of all protocol seeds. -/
noncomputable def executionLaw (p : Protocol X Y R SA SB) (μ : PMF (D × (X × Y))) :
    PMF (InformationSample D X Y R SA SB) :=
  FiniteLaw.joint μ (fun _ ↦ p.seedLaw)

def communicated (p : Protocol X Y R SA SB) (s : InformationSample D X Y R SA SB) :
    List Bool := ((p.tree s.2.1).run (s.1.2.1, s.2.2.1) (s.1.2.2, s.2.2.2)).1

def conditioning (s : InformationSample D X Y R SA SB) : D × R := (s.1.1, s.2.1)

/-- The transcript law in the information experiment agrees with the original
protocol's view law averaged over the input law. -/
theorem executionLaw_view (p : Protocol X Y R SA SB) (μ : PMF (D × (X × Y))) :
    (p.executionLaw μ).map (fun s ↦ (s.2.1, p.communicated s)) =
      μ.bind (fun s ↦ p.viewLaw s.2.1 s.2.2) := by
  simp only [executionLaw, FiniteLaw.joint_eq_bind, PMF.map_bind, PMF.map_comp,
    Function.comp_def, communicated, viewLaw]

variable [MeasurableSpace D] [DiscreteMeasurableSpace D]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

/-- External conditional information, in nats; no correctness assumption is needed. -/
noncomputable def informationCost (p : Protocol X Y R SA SB) (μ : PMF (D × (X × Y))) : ℝ :=
  condMutualInfo (fun s : InformationSample D X Y R SA SB ↦ s.1.2)
    p.communicated conditioning (p.executionLaw μ).toMeasure

local instance {E F : Type*} [Finite E] (f : E → F) : FiniteRange f := ⟨Set.finite_range f⟩

theorem executionLaw_indep (p : Protocol X Y R SA SB) (μ : PMF (D × (X × Y))) :
    IndepFun Prod.fst Prod.snd (p.executionLaw μ).toMeasure := by
  rw [executionLaw, FiniteLaw.joint_const_toMeasure]
  exact indepFun_fst_snd

theorem informationCost_nonneg (p : Protocol X Y R SA SB) (μ : PMF (D × (X × Y))) :
    0 ≤ p.informationCost μ :=
  condMutualInfo_nonneg .of_discrete .of_discrete

/-- Finite averaging over `(D,R)`, with zero mass assigned to null fibers. -/
theorem informationCost_eq_sum (p : Protocol X Y R SA SB) (μ : PMF (D × (X × Y))) :
    p.informationCost μ = ∑ z : D × R,
      (p.executionLaw μ).toMeasure.real (conditioning ⁻¹' {z}) *
        mutualInfo (fun s ↦ s.1.2) p.communicated
          ((p.executionLaw μ).toMeasure[|conditioning ⁻¹' {z}]) :=
  condMutualInfo_eq_sum' .of_discrete

/-- Communication bounds information for every finite input/analysis law.
The leaf support is bounded separately for each public seed before averaging. -/
theorem informationCost_le (p : Protocol X Y R SA SB) (μ : PMF (D × (X × Y))) :
    p.informationCost μ ≤ (p.cost : ℝ) * Real.log 2 := by
  apply InformationTools.condMutualInfo_le_of_fiber_support (p.executionLaw μ).toMeasure
    (fun s ↦ s.1.2) p.communicated conditioning (fun z : D × R ↦ (p.tree z.2).leafPaths)
  · intro s
    exact Tree.run_mem_leafPaths _ _ _
  · intro z
    exact p.card_leafPaths_le_cost z.2

/-- BJKS's `J(Π)` for disjointness, under the checked switch/input law. -/
noncomputable def bjksInformationCost {n : ℕ} (p : Protocol (Bits n) (Bits n) R SA SB) : ℝ :=
  p.informationCost (Switch.law n)

theorem bjksInformationCost_nonneg {n : ℕ} (p : Protocol (Bits n) (Bits n) R SA SB) :
    0 ≤ p.bjksInformationCost := p.informationCost_nonneg (Switch.law n)

theorem bjksInformationCost_le {n : ℕ} (p : Protocol (Bits n) (Bits n) R SA SB) :
    p.bjksInformationCost ≤ (p.cost : ℝ) * Real.log 2 :=
  p.informationCost_le (Switch.law n)

end Disjointness.Protocol
