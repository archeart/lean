module

public import BBCR.PrefixStructure

/-! Accumulated local divergence equals actual transcript information. All
expectations use the original input/private-seed execution law; terminated and
null histories contribute zero. This is the fixed-public-seed accounting in
Lemma 8.2. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.Prefix.Prior

variable {X Y R SA SB : Type*} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

local instance prefixAccountingFiniteRange {E F : Type*} [Finite E] (f : E → F) : FiniteRange f :=
  ⟨Set.finite_range f⟩

noncomputable def nodeDivergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (xy : X × Y) : ℝ :=
  aliceDivergence p μ r s xy + bobDivergence p μ r s xy

noncomputable def pathDivergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (n : ℕ) (ω : Sample X Y SA SB) : ℝ :=
  ∑ k ∈ Finset.range n, nodeDivergence p μ r (history p r k ω) ω.1

theorem stopped_information_zero (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (k : ℕ) (s : List Bool)
    (hstop : Tree.speaker (p.tree r) s = none) :
    mutualInfo Prod.fst (message p r k)
      ((execution p μ).toMeasure[|(history p r k) ⁻¹' {s}]) = 0 := by
  let ν := (execution p μ).toMeasure[|(history p r k) ⁻¹' {s}]
  have he : message p r k =ᵐ[ν] (fun _ ↦ false) :=
    ae_cond_of_forall_mem (show MeasurableSet ((history p r k) ⁻¹' {s}) from .of_discrete)
      (fun ω hω ↦ Tree.message_of_stopped (p.tree r) (ω.1.1,ω.2.1) (ω.1.2,ω.2.2) k
        (by
          change history p r k ω = s at hω
          change Tree.speaker (p.tree r) (history p r k ω) = none
          rw [hω, hstop]))
  have hid : IdentDistrib (fun ω ↦ (ω.1, message p r k ω))
      (fun ω : Sample X Y SA SB ↦ (ω.1,false)) ν ν :=
    IdentDistrib.of_ae_eq (.of_discrete) (he.mono fun _ h ↦ Prod.ext rfl h)
  rw [hid.mutualInfo_eq]
  exact mutualInfo_const (show Measurable (Prod.fst : Sample X Y SA SB → X × Y) from .of_discrete) false

/-- The local node statistic averaged on one active history is exactly the
actual conditional mutual information at that history. -/
theorem conditioned_node_average (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (hpos : 0 < prefixMass p μ r s) :
    (∑ ω, mass (conditioned p μ r s) ω * nodeDivergence p μ r s ω.1) =
      mutualInfo Prod.fst (message p r s.length)
        ((execution p μ).toMeasure[|(history p r s.length) ⁻¹' {s}]) := by
  rw [← Disjointness.Channel.sum_mass_map (conditioned p μ r s) Prod.fst
    (nodeDivergence p μ r s)]
  exact step_divergence_eq_information p μ r s who howner hpos

theorem weighted_node_average (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (k : ℕ) (s : List Bool)
    (hs : s ∈ FiniteRange.toFinset (history p r k)) :
    mass ((execution p μ).map (history p r k)) s *
        (∑ ω, mass (FiniteCondition.law (execution p μ) (history p r k) s) ω *
          nodeDivergence p μ r s ω.1) =
      (execution p μ).toMeasure.real ((history p r k) ⁻¹' {s}) *
        mutualInfo Prod.fst (message p r k)
          ((execution p μ).toMeasure[|(history p r k) ⁻¹' {s}]) := by
  simp only [measureReal_def, FiniteCondition.fiber_measure]
  change _ = mass ((execution p μ).map (history p r k)) s * _
  cases howner : Tree.speaker (p.tree r) s with
  | none =>
    simp [nodeDivergence, aliceDivergence, bobDivergence, howner,
      stopped_information_zero p μ r k s howner]
  | some who =>
    obtain ⟨ω,hω⟩ : ∃ ω, history p r k ω = s := by simpa using hs
    have hlen : s.length = k := by
      rw [← hω]
      exact Tree.active_history_length (p.tree r) (ω.1.1,ω.2.1) (ω.1.2,ω.2.2) k
        (by
          change Tree.speaker (p.tree r) (history p r k ω) ≠ none
          rw [hω, howner]
          exact Option.some_ne_none _)
    rw [← hlen]
    change prefixMass p μ r s * (∑ ω, mass (conditioned p μ r s) ω * _) = prefixMass p μ r s * _
    by_cases hp : 0 < prefixMass p μ r s
    · rw [conditioned_node_average p μ r s who howner hp]
    · have hz : prefixMass p μ r s = 0 :=
        le_antisymm (le_of_not_gt hp) (mass_nonneg _ _)
      simp [hz]

/-- Averaging the actual local KL costs over reached prefixes gives the
conditional information of the next transmitted bit. -/
theorem expected_step_divergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (k : ℕ) :
    (∑ ω, mass (execution p μ) ω * nodeDivergence p μ r (history p r k ω) ω.1) =
      stepInformation p r (execution p μ).toMeasure k := by
  rw [← FiniteCondition.sum_fibers (execution p μ) (history p r k)
    (fun s ω ↦ nodeDivergence p μ r s ω.1)]
  rw [stepInformation, condMutualInfo_eq_sum (show Measurable (history p r k) from .of_discrete)]
  exact Finset.sum_congr rfl fun s hs ↦ weighted_node_average p μ r k s hs

/-- Accumulated divergence up to any cutoff equals the information in the
corresponding actual transcript prefix, for an arbitrary correlated prior. -/
theorem expected_path_divergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (n : ℕ) :
    (∑ ω, mass (execution p μ) ω * pathDivergence p μ r n ω) =
      mutualInfo Prod.fst (history p r n) (execution p μ).toMeasure := by
  simp only [pathDivergence, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [expected_step_divergence]
  exact (information_history_chain p r (execution p μ).toMeasure n).symm

theorem expected_full_divergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (n : ℕ) (hn : (p.tree r).depth ≤ n) :
    (∑ ω, mass (execution p μ) ω * pathDivergence p μ r n ω) =
      mutualInfo Prod.fst (fun ω ↦ Experiment.transcript p r ω.1.1 ω.1.2 ω.2)
        (execution p μ).toMeasure := by
  rw [expected_path_divergence]
  have he : history p r n = fun ω ↦ Experiment.transcript p r ω.1.1 ω.1.2 ω.2 := by
    funext ω
    exact List.take_of_length_le ((Disjointness.Tree.run_length_le_depth _ _ _).trans hn)
  rw [he]

omit [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem nodeDivergence_nonneg (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (xy : X × Y)
    (hpos : 0 < prefixMass p μ r s) (hxy : mass (posterior p μ r s) xy ≠ 0) :
    0 ≤ nodeDivergence p μ r s xy := by
  have hs : Supported (Protocol.next p r xy.1 xy.2 s) (observerNext p μ r s) :=
    supported_mixture (posterior p μ r s) (fun xy ↦ Protocol.next p r xy.1 xy.2 s) xy hxy
  have hd := divergence_nonneg _ _ hs
  have hr := posterior_support_reach_pos p μ r s hpos xy hxy
  cases howner : Tree.speaker (p.tree r) s with
  | none => simp [nodeDivergence, aliceDivergence, bobDivergence, howner]
  | some who =>
    cases who with
    | alice =>
      rw [Protocol.next_eq_alice p r xy.1 xy.2 s howner hr] at hd
      simpa [nodeDivergence, aliceDivergence, bobDivergence, howner] using hd
    | bob =>
      rw [Protocol.next_eq_bob p r xy.1 xy.2 s howner hr] at hd
      simpa [nodeDivergence, aliceDivergence, bobDivergence, howner] using hd

omit [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem reached_posterior_support (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (k : ℕ) (ω : Sample X Y SA SB)
    (hω : mass (execution p μ) ω ≠ 0) :
    0 < prefixMass p μ r (history p r k ω) ∧
      mass (posterior p μ r (history p r k ω)) ω.1 ≠ 0 := by
  let s := history p r k ω
  have hh : history p r s.length ω = s := by
    have hp := List.take_prefix k (Experiment.transcript p r ω.1.1 ω.1.2 ω.2)
    exact (List.prefix_iff_eq_take.mp hp).symm
  have hm : 0 < mass (execution p μ) ω :=
    lt_of_le_of_ne (mass_nonneg _ _) (Ne.symm hω)
  have hs : 0 < prefixMass p μ r s := by
    have hl := FiniteCondition.mass_le_map (execution p μ) (history p r s.length) ω
    rw [hh] at hl
    exact hm.trans_le hl
  have hc : 0 < mass (conditioned p μ r s) ω := by
    rw [conditioned, FiniteCondition.mass_law_of_pos _ _ _ hs, ite_eq_left hh]
    exact div_pos hm hs
  have hxy : mass (posterior p μ r s) ω.1 ≠ 0 := by
    exact (hc.trans_le (FiniteCondition.mass_le_map (conditioned p μ r s) Prod.fst ω)).ne'
  exact ⟨hs,hxy⟩

omit [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem reached_node_nonneg (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (k : ℕ) (ω : Sample X Y SA SB)
    (hω : mass (execution p μ) ω ≠ 0) :
    0 ≤ nodeDivergence p μ r (history p r k ω) ω.1 := by
  obtain ⟨hs,hxy⟩ := reached_posterior_support p μ r k ω hω
  exact nodeDivergence_nonneg p μ r _ ω.1 hs hxy

omit [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem pathDivergence_nonneg (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (n : ℕ) (ω : Sample X Y SA SB)
    (hω : mass (execution p μ) ω ≠ 0) : 0 ≤ pathDivergence p μ r n ω :=
  Finset.sum_nonneg fun k _ ↦ reached_node_nonneg p μ r k ω hω

end BBCR.Prefix.Prior
