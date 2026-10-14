module

public import Disjointness.Tree

/-! # Transcript probability factorization from independent private seeds -/

@[expose] public section

open scoped ENNReal

namespace Disjointness.Protocol

variable {X Y R SA SB : Type*}

/-- Transcript law when the public seed is fixed, even at a zero-mass public seed. -/
noncomputable def privateTranscriptLaw (p : Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) : PMF (List Bool) :=
  p.aliceLaw.bind fun a ↦ p.bobLaw.map fun b ↦ ((p.tree r).run (x, a) (y, b)).1

/-- The fixed-public-seed law agrees with the joint execution definition. -/
theorem viewLaw_eq_bind_private (p : Protocol X Y R SA SB) (x : X) (y : Y) :
    p.viewLaw x y = p.publicLaw.bind fun r ↦
      (p.privateTranscriptLaw r x y).map fun t ↦ (r, t) := by
  simp [viewLaw, seedLaw, privateTranscriptLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Mass of a joint public-seed/transcript value. Zero-mass public seeds contribute zero. -/
theorem viewLaw_apply (p : Protocol X Y R SA SB) (x : X) (y : Y) (r : R) (t : List Bool) :
    p.viewLaw x y (r, t) = p.publicLaw r * p.privateTranscriptLaw r x y t := by
  classical
  rw [viewLaw_eq_bind_private, PMF.bind_apply]
  have h (r' : R) : ((p.privateTranscriptLaw r' x y).map fun s ↦ (r', s)) (r, t) =
      if r = r' then p.privateTranscriptLaw r' x y t else 0 := by
    by_cases hr : r = r' <;> simp [PMF.map_apply, hr]
  simp_rw [h, mul_ite, mul_zero]
  simp

open scoped Classical in
/-- Probability that Alice's private seed is consistent with the transcript. -/
noncomputable def aliceFactor [Fintype SA] (p : Protocol X Y R SA SB)
    (r : R) (t : List Bool) (x : X) : ℝ≥0∞ :=
  ∑ a, if (p.tree r).AliceConsistent (x, a) t then p.aliceLaw a else 0

open scoped Classical in
/-- Probability that Bob's private seed is consistent with the transcript. -/
noncomputable def bobFactor [Fintype SB] (p : Protocol X Y R SA SB)
    (r : R) (t : List Bool) (y : Y) : ℝ≥0∞ :=
  ∑ b, if (p.tree r).BobConsistent (y, b) t then p.bobLaw b else 0

/-- BJKS transcript factorization is a consequence of the model's locality and
independent private randomness. No rectangle assumption is supplied. -/
theorem privateTranscriptLaw_factorization [Fintype SA] [Fintype SB]
    (p : Protocol X Y R SA SB) (r : R) (t : List Bool) (x : X) (y : Y) :
    p.privateTranscriptLaw r x y t = p.aliceFactor r t x * p.bobFactor r t y := by
  classical
  simp only [privateTranscriptLaw, aliceFactor, bobFactor, PMF.bind_apply, PMF.map_apply,
    tsum_fintype, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h : (t = ((p.tree r).run (x, a) (y, b)).1) ↔
      (p.tree r).AliceConsistent (x, a) t ∧ (p.tree r).BobConsistent (y, b) t :=
    eq_comm.trans (Tree.run_transcript_eq_iff _ _ _ _)
  by_cases ha : (p.tree r).AliceConsistent (x, a) t <;>
    by_cases hb : (p.tree r).BobConsistent (y, b) t <;> simp [h, ha, hb]

/-- Joint-law version, retaining the public seed for correctness comparisons. -/
theorem viewLaw_factorization [Fintype SA] [Fintype SB]
    (p : Protocol X Y R SA SB) (r : R) (t : List Bool) (x : X) (y : Y) :
    p.viewLaw x y (r, t) = p.publicLaw r * (p.aliceFactor r t x * p.bobFactor r t y) := by
  rw [viewLaw_apply, privateTranscriptLaw_factorization]

/-- Each fixed-public-seed law is supported on actual leaf paths. -/
theorem privateTranscriptLaw_support (p : Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (t : List Bool)
    (ht : t ∈ (p.privateTranscriptLaw r x y).support) : t ∈ (p.tree r).leafPaths := by
  simp only [privateTranscriptLaw, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at ht
  obtain ⟨a, _, b, _, rfl⟩ := ht
  exact Tree.run_mem_leafPaths _ _ _

theorem depth_le_cost [Fintype R] (p : Protocol X Y R SA SB) (r : R) :
    (p.tree r).depth ≤ p.cost :=
  Finset.le_sup (f := fun r ↦ (p.tree r).depth) (Finset.mem_univ r)

/-- Pointwise transmitted-bit bound for every seed and input. -/
theorem run_length_le_cost [Fintype R] (p : Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (a : SA) (b : SB) :
    ((p.tree r).run (x, a) (y, b)).1.length ≤ p.cost :=
  (Tree.run_length_le_depth _ _ _).trans (depth_le_cost p r)

/-- Support-size bound independent of the public seed's cardinality. -/
theorem card_leafPaths_le_cost [Fintype R] (p : Protocol X Y R SA SB) (r : R) :
    (p.tree r).leafPaths.card ≤ 2 ^ p.cost :=
  (Tree.card_leafPaths_le _).trans (Nat.pow_le_pow_right (by decide) (depth_le_cost p r))

end Disjointness.Protocol
