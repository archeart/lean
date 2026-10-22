module

public import BBCR.LikelihoodAccounting
public import BBCR.PublicInformation

/-! The root residual potential is the original protocol's expected path
information, and its public/input average is external information. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.StoppingFrontier

theorem hit_eq_self (n : ℕ) (halt : List Bool → Bool) (s bits : List Bool)
    (hlen : bits.length ≤ n) (hpre : ∀ j < bits.length, halt (s ++ bits.take j) = false) :
    hit n halt s bits = bits := by
  induction n generalizing s bits with
  | zero =>
    have he : bits = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    simp [hit, he]
  | succ n ih =>
    cases bits with
    | nil => simp [hit]
    | cons b bits =>
      have hs := hpre 0 (by simp)
      simp only [List.take_zero, List.append_nil] at hs
      rw [hit, hs]
      simp only [Bool.false_eq_true, ite_false]
      congr 1
      apply ih (s ++ [b]) bits (by simpa using hlen)
      intro j hj
      simpa using hpre (j + 1) (by simpa using Nat.succ_lt_succ hj)

end BBCR.StoppingFrontier

namespace BBCR.FiniteCondition

theorem law_const {Ω A : Type*} [Fintype Ω] (p : PMF Ω) (a : A) : law p (fun _ ↦ a) a = p := by
  have hp : 0 < mass (p.map (fun _ ↦ a)) a := by simp [map_constant, mass]
  apply PMF.ext
  intro ω
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change mass _ _ = mass _ _
  rw [mass_law_of_pos p (fun _ ↦ a) a hp ω]
  simp [map_constant, mass]

end BBCR.FiniteCondition

namespace BBCR.StoppedAzuma

theorem map_subtype_injective {A : Type*} {S : A → Prop} {p q : PMF {a // S a}}
    (h : p.map Subtype.val = q.map Subtype.val) : p = q := by
  apply PMF.ext
  intro a
  rw [← map_subtype_apply p a, ← map_subtype_apply q a, h]

theorem pathSum_range (d : List Bool → ℝ) (s w : List Bool) :
    pathSum d s w = ∑ j ∈ Finset.range w.length, d (s ++ w.take j) := by
  induction w using List.reverseRecOn with
  | nil => simp [pathSum]
  | append_singleton w b ih =>
    have he : pathSum d s (w ++ [b]) = pathSum d s w + d (s ++ w) := by
      clear ih
      induction w generalizing s with
      | nil => simp [pathSum]
      | cons a w hh => simp [pathSum, hh, List.append_assoc, add_assoc]
    rw [he, ih]
    simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [List.take_append_of_le_length (Nat.le_of_lt (Finset.mem_range.mp hj))]
    · simp

end BBCR.StoppedAzuma

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier Prefix

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem leaf_hit (p : Disjointness.Protocol X Y R SA SB) (r : R) (xy : X × Y) (ω : SA × SB) :
    StoppingFrontier.hit (p.tree r).depth (terminal p r) [] (Experiment.transcript p r xy.1 xy.2 ω) =
      Experiment.transcript p r xy.1 xy.2 ω := by
  apply StoppingFrontier.hit_eq_self
  · exact Disjointness.Tree.run_length_le_depth _ _ _
  · intro j hj
    have hn : Tree.speaker (p.tree r) ((Experiment.transcript p r xy.1 xy.2 ω).take j) ≠ none := by
      intro hh
      have hh' := (Tree.speaker_take_eq_none_iff (p.tree r) (xy.1,ω.1) (xy.2,ω.2) j).mp hh
      exact Nat.not_le_of_gt hj hh'
    simp [terminal, hn]

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem transcript_mem (p : Disjointness.Protocol X Y R SA SB) (r : R) (xy : X × Y) (ω : SA × SB) :
    Experiment.transcript p r xy.1 xy.2 ω ∈ StoppingFrontier.paths (p.tree r).depth (terminal p r) [] := by
  rw [← leaf_hit p r xy ω]
  apply StoppingFrontier.hit_mem
  · exact Disjointness.Tree.run_length_le_depth _ _ _
  · have hn := (Tree.speaker_take_eq_none_iff (p.tree r) (xy.1,ω.1) (xy.2,ω.2)
      ((p.tree r).run (xy.1,ω.1) (xy.2,ω.2)).1.length).mpr le_rfl
    simp only [List.take_length] at hn
    simp only [terminal, decide_eq_true_eq, List.nil_append]
    exact hn

noncomputable def actualLeaf (p : Disjointness.Protocol X Y R SA SB) (r : R) (xy : X × Y) (ω : SA × SB) :
    ↥(StoppingFrontier.paths (p.tree r).depth (terminal p r) []) :=
  ⟨Experiment.transcript p r xy.1 xy.2 ω, transcript_mem p r xy ω⟩

theorem leaf_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (r : R) (xy : X × Y) :
    StoppingFrontier.finiteLaw (p.tree r).depth (terminal p r) (targetKernel p μ r xy) [] =
      (Experiment.privateSeeds p).map (actualLeaf p r xy) := by
  apply StoppedAzuma.map_subtype_injective
  rw [StoppingFrontier.finiteLaw_map_val, PMF.map_comp]
  change StoppingFrontier.law _ _ _ [] = (Experiment.privateSeeds p).map (Experiment.transcript p r xy.1 xy.2)
  have hpos : 0 < StoppingFrontier.prefixProbability (Experiment.privateSeeds p)
      (Experiment.transcript p r xy.1 xy.2) [] := by
    simp [StoppingFrontier.prefixProbability, map_constant, mass]
  rw [StoppingFrontier.law_eq_stoppedExecution (Experiment.privateSeeds p)
    (Experiment.transcript p r xy.1 xy.2) (p.tree r).depth (terminal p r) (targetKernel p μ r xy) ?_ [] hpos ?_ ?_]
  · simp only [StoppingFrontier.stoppedExecution, List.length_nil, List.take_zero, List.drop_zero,
      FiniteCondition.law_const, leaf_hit]
  · intro s hs b
    have hn : Tree.speaker (p.tree r) s ≠ none := by simpa [terminal] using hs
    obtain ⟨who,howner⟩ := Option.ne_none_iff_exists'.mp hn
    simp only [private_prefixProbability]
    exact weighted_targetKernel p μ r xy s who howner b
  · intro ω
    exact Disjointness.Tree.run_length_le_depth _ _ _
  · intro ω
    have hn := (Tree.speaker_take_eq_none_iff (p.tree r) (xy.1,ω.1) (xy.2,ω.2)
      ((p.tree r).run (xy.1,ω.1) (xy.2,ω.2)).1.length).mpr le_rfl
    simp only [List.take_length] at hn
    simp only [terminal, decide_eq_true_eq]
    exact hn

theorem pathSum_eq_divergence (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (ω : SA × SB) (n : ℕ) (hn : (p.tree r).depth ≤ n) :
    StoppedAzuma.pathSum (fun s ↦ Prior.nodeDivergence p μ r s xy) [] (Experiment.transcript p r xy.1 xy.2 ω) =
      Prior.pathDivergence p μ r n (xy,ω) := by
  rw [StoppedAzuma.pathSum_range]
  simp only [List.nil_append]
  let T := Experiment.transcript p r xy.1 xy.2 ω
  have hlen : T.length ≤ n := (Disjointness.Tree.run_length_le_depth _ _ _).trans hn
  change (∑ j ∈ Finset.range T.length, Prior.nodeDivergence p μ r (T.take j) xy) =
    ∑ j ∈ Finset.range n, Prior.nodeDivergence p μ r (T.take j) xy
  rw [show n = T.length + (n - T.length) by omega, Finset.sum_range_add]
  rw [show (∑ j ∈ Finset.range (n - T.length), Prior.nodeDivergence p μ r (T.take (T.length + j)) xy) = 0 from ?_, add_zero]
  apply Finset.sum_eq_zero
  intro j _
  have hstop := (Tree.speaker_take_eq_none_iff (p.tree r) (xy.1,ω.1) (xy.2,ω.2) (T.length + j)).mpr (by change T.length ≤ T.length + j; omega)
  change Tree.speaker (p.tree r) (T.take (T.length + j)) = none at hstop
  simp [Prior.nodeDivergence, Prior.aliceDivergence, Prior.bobDivergence, hstop]

theorem residual_root (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (r : R) (xy : X × Y) :
    residual p μ r xy [] = ∑ ω, mass (Experiment.privateSeeds p) ω *
      Prior.pathDivergence p μ r (p.tree r).depth (xy,ω) := by
  unfold residual KernelPotential.value
  simp only [List.length_nil, Nat.sub_zero]
  rw [KernelPotential.future_eq_expect, leaf_law p μ r xy, FiniteAzuma.expect_map]
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  exact pathSum_eq_divergence p μ r xy ω _ le_rfl

theorem residual_root_cutoff (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (n : ℕ) (hn : (p.tree r).depth ≤ n) :
    residual p μ r xy [] = ∑ ω, mass (Experiment.privateSeeds p) ω * Prior.pathDivergence p μ r n (xy,ω) := by
  rw [residual_root]
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  rw [← pathSum_eq_divergence p μ r xy ω _ le_rfl,
    ← pathSum_eq_divergence p μ r xy ω n hn]

variable [Fintype R]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

/-- The total available potential is exactly the original external information. -/
theorem average_residual_root (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    (∑ r, mass p.publicLaw r * ∑ xy, mass μ xy * residual p μ r xy []) = externalInformation p μ := by
  rw [← expected_divergence_eq_externalInformation]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  simp_rw [residual_root_cutoff p μ r _ p.cost (p.depth_le_cost r)]
  simp only [Fintype.sum_prod_type, Prior.execution, Experiment.privateSeeds,
    Disjointness.FiniteLaw.joint_apply, mass, ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]

end BBCR.LikelihoodFrontier
