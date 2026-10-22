module

public import BBCR.PrefixAccounting

/-! The conditional interval form of the divergence accounting. Conditioning on
an initial prefix does not change the later full-history kernels. This is
proved by finite disintegration and refinement of the observed history. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.Prefix.Prior

variable {X Y R SA SB : Type*}

theorem history_refines (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (i k : ℕ) (hik : i ≤ k) : history p r i = List.take i ∘ history p r k := by
  funext ω
  simp [history, Experiment.history, List.take_take, Nat.min_eq_left hik]

variable [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

local instance conditionalAccountingFiniteRange {E F : Type*} [Finite E] (f : E → F) : FiniteRange f :=
  ⟨Set.finite_range f⟩

theorem information_history_interval (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (ν : Measure (Sample X Y SA SB)) [IsZeroOrProbabilityMeasure ν]
    (i j : ℕ) (hij : i ≤ j) :
    mutualInfo Prod.fst (history p r j) ν = mutualInfo Prod.fst (history p r i) ν +
      ∑ k ∈ Finset.Ico i j, stepInformation p r ν k := by
  rw [information_history_chain, information_history_chain]
  exact (Finset.sum_range_add_sum_Ico _ hij).symm

theorem conditional_step_divergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (i k : ℕ) (hik : i ≤ k) (s : List Bool)
    (hpos : 0 < mass ((execution p μ).map (history p r i)) s) :
    let q := FiniteCondition.law (execution p μ) (history p r i) s
    (∑ ω, mass q ω * nodeDivergence p μ r (history p r k ω) ω.1) =
      stepInformation p r q.toMeasure k := by
  dsimp only
  rw [← FiniteCondition.sum_fibers _ (history p r k) (fun t ω ↦ nodeDivergence p μ r t ω.1)]
  rw [stepInformation, condMutualInfo_eq_sum (show Measurable (history p r k) from .of_discrete)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [measureReal_def, FiniteCondition.fiber_measure]
  change _ = mass ((FiniteCondition.law (execution p μ) (history p r i) s).map (history p r k)) t * _
  by_cases hp : 0 < mass ((FiniteCondition.law (execution p μ) (history p r i) s).map (history p r k)) t
  · have href := history_refines p r i k hik
    have hinit : 0 < mass ((execution p μ).map (List.take i ∘ history p r k)) s := by
      rwa [← href]
    have hpost : 0 < mass ((FiniteCondition.law (execution p μ)
        (List.take i ∘ history p r k) s).map (history p r k)) t := by rwa [← href]
    have hbase := (FiniteCondition.refinement_of_positive (execution p μ) (history p r k)
      (List.take i) s t hinit hpost).2
    have hlaw := FiniteCondition.law_refinement (execution p μ) (history p r k)
      (List.take i) s t hinit hpost
    rw [← href] at hlaw
    have hnode := weighted_node_average p μ r k t ht
    rw [measureReal_def, FiniteCondition.fiber_measure] at hnode
    have hunit := mul_left_cancel₀ hbase.ne' hnode
    congr 1
    rw [← FiniteCondition.toMeasure_law_of_pos _ (history p r k) t hp, hlaw,
      FiniteCondition.toMeasure_law_of_pos _ (history p r k) t hbase]
    exact hunit
  · have hz : mass ((FiniteCondition.law (execution p μ) (history p r i) s).map (history p r k)) t = 0 :=
      le_antisymm (le_of_not_gt hp) (mass_nonneg _ _)
    simp [hz]

noncomputable def intervalDivergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (i j : ℕ) (ω : Sample X Y SA SB) : ℝ :=
  ∑ k ∈ Finset.Ico i j, nodeDivergence p μ r (history p r k ω) ω.1

/-- Lemma 8.2 on every positive initial-prefix fiber, in the finite model.
The local kernels retain their original prior. No conditional information or
conditional independence is assumed as a hypothesis. -/
theorem conditional_interval_divergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (i j : ℕ) (hij : i ≤ j) (s : List Bool)
    (hpos : 0 < mass ((execution p μ).map (history p r i)) s) :
    let q := FiniteCondition.law (execution p μ) (history p r i) s
    (∑ ω, mass q ω * intervalDivergence p μ r i j ω) =
      mutualInfo Prod.fst (history p r j)
        ((execution p μ).toMeasure[|(history p r i) ⁻¹' {s}]) := by
  let q := FiniteCondition.law (execution p μ) (history p r i) s
  have hq : q.toMeasure = (execution p μ).toMeasure[|(history p r i) ⁻¹' {s}] :=
    FiniteCondition.toMeasure_law_of_pos _ _ _ hpos
  have he : history p r i =ᵐ[q.toMeasure] (fun _ ↦ s) := by
    rw [hq]
    exact ae_cond_of_forall_mem (.of_discrete) (fun _ h ↦ h)
  have hid : IdentDistrib (fun ω ↦ (ω.1, history p r i ω))
      (fun ω : Sample X Y SA SB ↦ (ω.1,s)) q.toMeasure q.toMeasure :=
    IdentDistrib.of_ae_eq (.of_discrete) (he.mono fun _ h ↦ Prod.ext rfl h)
  have hzero : mutualInfo Prod.fst (history p r i) q.toMeasure = 0 := by
    rw [hid.mutualInfo_eq]
    exact mutualInfo_const (.of_discrete) s
  have hchain := information_history_interval p r q.toMeasure i j hij
  rw [hzero, zero_add] at hchain
  dsimp only
  simp only [intervalDivergence, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k ∈ Finset.Ico i j, stepInformation p r q.toMeasure k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact conditional_step_divergence p μ r i k (Finset.mem_Ico.mp hk).1 s hpos
    _ = _ := by rw [← hchain, hq]

/-- Measure-theoretic form of Lemma 8.2, including null initial histories. The
interval is half-open, using zero-based message indices. In this finite private-
randomness model the paper's inequality holds with equality. -/
theorem conditional_interval_divergence_measure (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (i j : ℕ) (hij : i ≤ j) (s : List Bool) :
    let ν := (execution p μ).toMeasure[|(history p r i) ⁻¹' {s}]
    (∑ ω, ν.real {ω} * intervalDivergence p μ r i j ω) =
      mutualInfo Prod.fst (history p r j) ν := by
  dsimp only
  by_cases hp : 0 < mass ((execution p μ).map (history p r i)) s
  · have hq := FiniteCondition.toMeasure_law_of_pos (execution p μ) (history p r i) s hp
    rw [← hq]
    simp only [measureReal_def, PMF.toMeasure_apply_singleton _ _ (.singleton _)]
    have hc := conditional_interval_divergence p μ r i j hij s hp
    rw [← hq] at hc
    exact hc
  · have hz : mass ((execution p μ).map (history p r i)) s = 0 :=
      le_antisymm (le_of_not_gt hp) (mass_nonneg _ _)
    have hm : ((execution p μ).map (history p r i)) s = 0 := by
      apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (by simp)).mp
      exact hz
    have hf : (execution p μ).toMeasure ((history p r i) ⁻¹' {s}) = 0 := by
      rw [FiniteCondition.fiber_measure, hm]
    rw [cond_eq_zero_of_meas_eq_zero hf]
    simp [mutualInfo_def]

end BBCR.Prefix.Prior
