module

public import BBCR.LikelihoodBounds

/-! Explicit trial counts and communication cutoffs for the actual simulator. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.LikelihoodFrontier

noncomputable def trialScale (I α : ℝ) : ℝ :=
  32 * I / (acceptanceRate * α) + 8 * Real.log (4 / α) / acceptanceRate ^ 2

noncomputable def trialCount (I α : ℝ) : ℕ := ⌈trialScale I α⌉₊ + 1

noncomputable def bitCutoff (C : ℕ) (I α : ℝ) : ℕ :=
  4 * trialCount I α + ⌈4 * communicationCoefficient C * I / α⌉₊ + 1

theorem trialCount_pos (I α : ℝ) : 0 < trialCount I α := by unfold trialCount; omega

theorem bitCutoff_gt (C : ℕ) (I α : ℝ) : 4 * trialCount I α < bitCutoff C I α := by unfold bitCutoff; omega

theorem trialScale_nonneg (I α : ℝ) (hI : 0 ≤ I) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) : 0 ≤ trialScale I α := by
  unfold trialScale
  have hρ := acceptanceRate_pos
  have hl : 0 ≤ Real.log (4 / α) := Real.log_nonneg ((le_div_iff₀ hα).mpr (by linarith))
  positivity

theorem parameter_error (C : ℕ) (I α : ℝ) (hI : 0 ≤ I) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) :
    communicationCoefficient C * I / ((bitCutoff C I α : ℝ) - 4 * trialCount I α) +
      8 * I / (acceptanceRate * trialCount I α) +
      Real.exp (-(acceptanceRate ^ 2 * trialCount I α / 8)) ≤ α := by
  let N := trialCount I α
  let Q := bitCutoff C I α
  have hρ := acceptanceRate_pos
  have hA := communicationCoefficient_nonneg C
  have hN : (0 : ℝ) < N := by exact_mod_cast trialCount_pos I α
  have hQ : 0 < (Q : ℝ) - 4 * N := by
    have hh : (4 : ℝ) * N < Q := by exact_mod_cast bitCutoff_gt C I α
    linarith
  have hscale : trialScale I α ≤ (N : ℝ) := (Nat.le_ceil _).trans (by simp [N,trialCount])
  have hl : 0 ≤ Real.log (4 / α) := Real.log_nonneg ((le_div_iff₀ hα).mpr (by linarith))
  have hfirst : 8 * I / (acceptanceRate * N) ≤ α / 4 := by
    apply (div_le_iff₀ (mul_pos hρ hN)).mpr
    have hh : 32 * I / (acceptanceRate * α) ≤ (N : ℝ) := by
      have he : 0 ≤ 8 * Real.log (4 / α) / acceptanceRate ^ 2 := by positivity
      unfold trialScale at hscale
      linarith
    have hm := (div_le_iff₀ (mul_pos hρ hα)).mp hh
    nlinarith
  have hsecond : communicationCoefficient C * I / ((Q : ℝ) - 4 * N) ≤ α / 4 := by
    apply (div_le_iff₀ hQ).mpr
    have hh := Nat.le_ceil (4 * communicationCoefficient C * I / α)
    have he : 4 * communicationCoefficient C * I / α ≤ (Q : ℝ) - 4 * N := by
      dsimp only [Q,bitCutoff,N]
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      linarith
    have hm := (div_le_iff₀ hα).mp he
    nlinarith
  have hexp : Real.exp (-(acceptanceRate ^ 2 * N / 8)) ≤ α / 4 := by
    have hh : 8 * Real.log (4 / α) / acceptanceRate ^ 2 ≤ (N : ℝ) := by
      have he : 0 ≤ 32 * I / (acceptanceRate * α) := by positivity
      unfold trialScale at hscale
      linarith
    have hm := (div_le_iff₀ (sq_pos_of_pos hρ)).mp hh
    have he : -(acceptanceRate ^ 2 * N / 8) ≤ Real.log (α / 4) := by
      rw [show α / 4 = (4 / α)⁻¹ by field_simp, Real.log_inv]
      linarith
    exact (Real.exp_le_exp.mpr he).trans_eq (Real.exp_log (by positivity))
  change _ ≤ α
  dsimp only [N,Q] at hfirst hsecond hexp
  linarith

end BBCR.LikelihoodFrontier
