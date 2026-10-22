module

public import BBCR.PrefixExperiment
public import Disjointness.InformationCost
public import BBCR.TranscriptChain

/-! One-step divergence accounting at a reached protocol prefix, for an
arbitrary correlated input prior. All conditional kernels are linked to the
actual input/private-seed execution law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger
open scoped Classical

namespace BBCR.Prefix.Prior

variable {X Y R SA SB : Type*} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

abbrev Sample (X Y SA SB : Type*) := (X × Y) × (SA × SB)

noncomputable def execution (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    PMF (Sample X Y SA SB) := joint μ (fun _ ↦ Experiment.privateSeeds p)

def history (p : Disjointness.Protocol X Y R SA SB) (r : R) (k : ℕ)
    (ω : Sample X Y SA SB) : List Bool := Experiment.history p r ω.1.1 ω.1.2 k ω.2

def message (p : Disjointness.Protocol X Y R SA SB) (r : R) (k : ℕ)
    (ω : Sample X Y SA SB) : Bool := Experiment.message p r ω.1.1 ω.1.2 k ω.2

theorem execution_input_prefix (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (k : ℕ) :
    (execution p μ).map (fun ω ↦ (ω.1, history p r k ω)) =
      FiniteCondition.jointLaw μ (fun xy ↦ Protocol.law p r xy.1 xy.2 k) := by
  conv_rhs => simp only [← Experiment.privateSeeds_history p r]
  simp only [execution, joint_eq_bind, FiniteCondition.jointLaw, PMF.map_bind,
    PMF.map_comp, Function.comp_def, history]

theorem execution_prefix (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (k : ℕ) :
    (execution p μ).map (history p r k) = μ.bind (fun xy ↦ Protocol.law p r xy.1 xy.2 k) := by
  have h := congrArg (fun q : PMF ((X × Y) × List Bool) ↦ q.map Prod.snd)
    (execution_input_prefix p μ r k)
  simpa only [PMF.map_comp, Function.comp_def, FiniteCondition.jointLaw_map_snd] using h

noncomputable def prefixMass (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) : ℝ :=
  mass ((execution p μ).map (history p r s.length)) s

noncomputable def conditioned (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) : PMF (Sample X Y SA SB) :=
  FiniteCondition.law (execution p μ) (history p r s.length) s

noncomputable def posterior (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) : PMF (X × Y) :=
  (conditioned p μ r s).map Prod.fst

theorem weighted_posterior (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (xy : X × Y) :
    prefixMass p μ r s * mass (posterior p μ r s) xy = mass μ xy * Protocol.reach p r xy.1 xy.2 s := by
  rw [prefixMass, posterior, conditioned, FiniteCondition.weighted_pair,
    execution_input_prefix]
  simp only [mass, FiniteCondition.jointLaw_apply, ENNReal.toReal_mul, Protocol.reach]

theorem prefixMass_eq_sum (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) :
    prefixMass p μ r s = ∑ xy, mass μ xy * Protocol.reach p r xy.1 xy.2 s := by
  rw [prefixMass, execution_prefix, Disjointness.Channel.mass_bind]
  rfl

theorem posterior_support_reach_pos (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (hpos : 0 < prefixMass p μ r s)
    (xy : X × Y) (hxy : mass (posterior p μ r s) xy ≠ 0) :
    0 < Protocol.reach p r xy.1 xy.2 s := by
  have hn : mass μ xy * Protocol.reach p r xy.1 xy.2 s ≠ 0 := by
    rw [← weighted_posterior]
    exact mul_ne_zero hpos.ne' hxy
  exact lt_of_le_of_ne (Protocol.reach_nonneg _ _ _ _ _) (Ne.symm (mul_ne_zero_iff.mp hn).2)

theorem weighted_input_message (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (xy : X × Y) (bit : Bool) :
    prefixMass p μ r s * mass ((conditioned p μ r s).map
      (fun ω ↦ (ω.1, message p r s.length ω))) (xy,bit) =
      mass μ xy * Protocol.reach p r xy.1 xy.2 (s ++ [bit]) := by
  rw [prefixMass, conditioned, FiniteCondition.weighted_pair]
  have he : mass ((execution p μ).map
      (fun ω ↦ ((ω.1, message p r s.length ω), history p r s.length ω))) ((xy,bit),s) =
      mass ((execution p μ).map (fun ω ↦ (ω.1, history p r (s ++ [bit]).length ω))) (xy,s ++ [bit]) := by
    rw [Disjointness.Channel.event_mass, Disjointness.Channel.event_mass]
    simp only [Finset.sum_filter, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro ω _
    have hh := Experiment.extension_event p r ω.1.1 ω.1.2 s who howner bit ω.2
    change (Experiment.history p r ω.1.1 ω.1.2 s.length ω.2 = s ∧
      Experiment.message p r ω.1.1 ω.1.2 s.length ω.2 = bit) ↔
      Experiment.history p r ω.1.1 ω.1.2 (s ++ [bit]).length ω.2 = s ++ [bit] at hh
    by_cases hi : ω.1 = xy
    · simp only [hi, true_and]
      have hpred : message p r s.length ω = bit ∧ history p r s.length ω = s ↔
          history p r (s ++ [bit]).length ω = s ++ [bit] := by
        simpa only [message, history, and_comm] using hh
      simp only [hpred]
    · simp [hi]
  rw [he, execution_input_prefix]
  simp only [mass, FiniteCondition.jointLaw_apply, ENNReal.toReal_mul, Protocol.reach]

/-- Exact disintegration of the actual conditional input/message law. -/
theorem conditioned_input_message (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (hpos : 0 < prefixMass p μ r s) :
    joint (posterior p μ r s) (fun xy ↦ Protocol.next p r xy.1 xy.2 s) =
      (conditioned p μ r s).map (fun ω ↦ (ω.1, message p r s.length ω)) := by
  apply PMF.ext
  rintro ⟨xy,bit⟩
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  apply mul_left_cancel₀ hpos.ne'
  change prefixMass p μ r s * mass (joint _ _) (xy,bit) = _
  simp only [mass, joint_apply, ENNReal.toReal_mul]
  change prefixMass p μ r s * (mass (posterior p μ r s) xy *
      mass (Protocol.next p r xy.1 xy.2 s) bit) = _
  calc
    _ = (prefixMass p μ r s * mass (posterior p μ r s) xy) *
        mass (Protocol.next p r xy.1 xy.2 s) bit := by ring
    _ = mass μ xy * (Protocol.reach p r xy.1 xy.2 s * mass (Protocol.next p r xy.1 xy.2 s) bit) := by
      rw [weighted_posterior]; ring
    _ = mass μ xy * Protocol.reach p r xy.1 xy.2 (s ++ [bit]) := by
      rw [Protocol.weighted_mass_next p r xy.1 xy.2 s who howner bit]
    _ = _ := (weighted_input_message p μ r s who howner xy bit).symm

noncomputable def observerNext (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) : PMF Bool :=
  (posterior p μ r s).bind (fun xy ↦ Protocol.next p r xy.1 xy.2 s)

section Information

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

theorem information_next_eq_actual (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (hpos : 0 < prefixMass p μ r s) :
    Disjointness.Channel.information (posterior p μ r s) (fun xy ↦ Protocol.next p r xy.1 xy.2 s) =
      mutualInfo Prod.fst (message p r s.length) (conditioned p μ r s).toMeasure := by
  unfold Disjointness.Channel.information
  apply IdentDistrib.mutualInfo_eq
  refine ⟨.of_discrete, .of_discrete, ?_⟩
  change (joint _ _).toMeasure.map id =
    (conditioned p μ r s).toMeasure.map (fun ω ↦ (ω.1, message p r s.length ω))
  rw [Measure.map_id, PMF.toMeasure_map _ _ (.of_discrete),
    conditioned_input_message p μ r s who howner hpos]

/-- The one-step form of Lemma 8.2 at an Alice node, with the conditional
mutual information computed from actual execution on an arbitrary input prior. -/
theorem alice_divergence_eq_information (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool)
    (howner : Tree.speaker (p.tree r) s = some .alice) (hpos : 0 < prefixMass p μ r s) :
    (∑ xy, mass (posterior p μ r s) xy *
      divergence (Protocol.aliceNext p r s xy.1) (observerNext p μ r s)) =
      mutualInfo Prod.fst (message p r s.length) (conditioned p μ r s).toMeasure := by
  rw [← information_next_eq_actual p μ r s .alice howner hpos,
    information_eq_average_divergence]
  apply Finset.sum_congr rfl
  intro xy _
  by_cases hx : mass (posterior p μ r s) xy = 0
  · simp [hx]
  · rw [Protocol.next_eq_alice p r xy.1 xy.2 s howner
      (posterior_support_reach_pos p μ r s hpos xy hx)]
    rfl

theorem bob_divergence_eq_information (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool)
    (howner : Tree.speaker (p.tree r) s = some .bob) (hpos : 0 < prefixMass p μ r s) :
    (∑ xy, mass (posterior p μ r s) xy *
      divergence (Protocol.bobNext p r s xy.2) (observerNext p μ r s)) =
      mutualInfo Prod.fst (message p r s.length) (conditioned p μ r s).toMeasure := by
  rw [← information_next_eq_actual p μ r s .bob howner hpos,
    information_eq_average_divergence]
  apply Finset.sum_congr rfl
  intro xy _
  by_cases hx : mass (posterior p μ r s) xy = 0
  · simp [hx]
  · rw [Protocol.next_eq_bob p r xy.1 xy.2 s howner
      (posterior_support_reach_pos p μ r s hpos xy hx)]
    rfl

theorem conditioned_toMeasure (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (hpos : 0 < prefixMass p μ r s) :
    (conditioned p μ r s).toMeasure =
      (execution p μ).toMeasure[|(history p r s.length) ⁻¹' {s}] :=
  FiniteCondition.toMeasure_law_of_pos _ _ _ hpos

noncomputable def aliceDivergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (xy : X × Y) : ℝ :=
  if Tree.speaker (p.tree r) s = some .alice then
    divergence (Protocol.aliceNext p r s xy.1) (observerNext p μ r s) else 0

noncomputable def bobDivergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (xy : X × Y) : ℝ :=
  if Tree.speaker (p.tree r) s = some .bob then
    divergence (Protocol.bobNext p r s xy.2) (observerNext p μ r s) else 0

/-- The actual one-step divergence accounting in Lemma 8.2, including both
players' costs and PFR's measure-theoretic conditioning on the reached prefix. -/
theorem step_divergence_eq_information (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (hpos : 0 < prefixMass p μ r s) :
    (∑ xy, mass (posterior p μ r s) xy *
      (aliceDivergence p μ r s xy + bobDivergence p μ r s xy)) =
      mutualInfo Prod.fst (message p r s.length)
        ((execution p μ).toMeasure[|(history p r s.length) ⁻¹' {s}]) := by
  rw [← conditioned_toMeasure p μ r s hpos]
  cases who with
  | alice =>
    simpa [aliceDivergence, bobDivergence, howner] using
      alice_divergence_eq_information p μ r s howner hpos
  | bob =>
    simpa [aliceDivergence, bobDivergence, howner] using
      bob_divergence_eq_information p μ r s howner hpos

/-- The conditional interval chain rule specialized to the actual protocol
execution. Optional next bits explicitly account for stopping at a leaf. -/
theorem interval_information_actual (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (i j : ℕ) (hij : i ≤ j) (s : List Bool) :
    let ν := (execution p μ).toMeasure[|(history p r i) ⁻¹' {s}]
    (∑ k ∈ Finset.Ico i j, transcriptStepInformation ν Prod.fst
      (fun ω ↦ Experiment.transcript p r ω.1.1 ω.1.2 ω.2) k) =
      mutualInfo Prod.fst (history p r j) ν :=
  information_interval_given_prefix _ _ _ i j hij s

end Information
end BBCR.Prefix.Prior
