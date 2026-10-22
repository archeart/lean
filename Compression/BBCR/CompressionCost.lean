module

public import BBCR.CompressionParameters
public import BBCR.SmoothingScale

/-! The explicit bounded simulator has the single-logarithm information budget. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.LikelihoodFrontier

noncomputable def compressionConstant : ℝ :=
  20 + 256 / acceptanceRate + 96 / acceptanceRate ^ 2 + 192 * Real.exp 4 / acceptanceRate

theorem compressionConstant_pos : 0 < compressionConstant := by
  unfold compressionConstant
  have hρ := acceptanceRate_pos
  positivity

theorem index_width_le (C : ℕ) (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) :
    (FrontierLocation.width C : ℝ) ≤ 6 * Real.log (((C : ℝ) + 1) / α) := by
  let L := Real.log (((C : ℝ) + 1) / α)
  have hL : 1 / 2 ≤ L := SmoothingCoupling.smoothingScale_half_le C α hα hα₁
  have hlog : Real.log ((C : ℝ) + 1) ≤ L := by
    apply Real.log_le_log (by positivity)
    exact (le_div_iff₀ hα).mpr (by nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C])
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  let w := FrontierLocation.width C
  by_cases hw : w = 0
  · change (w : ℝ) ≤ 6 * L
    rw [hw]
    norm_num
    linarith
  · have hw₀ : 0 < w := Nat.pos_of_ne_zero hw
    have hp : 2 ^ (w - 1) < C + 1 := (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by
      change w - 1 < w
      omega)
    have hp' : (2 : ℝ) ^ (w - 1) < (C : ℝ) + 1 := by exact_mod_cast hp
    have hh := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ (w - 1)) hp'
    rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ w), Nat.cast_one] at hh
    have hw₁ : (1 : ℝ) ≤ w := by exact_mod_cast hw₀
    have hmul := mul_le_mul_of_nonneg_left htwo (by linarith : (0 : ℝ) ≤ (w : ℝ) - 1)
    change (w : ℝ) ≤ 6 * L
    linarith

theorem log_four_div_le (C : ℕ) (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) :
    Real.log (4 / α) ≤ 3 * Real.log (((C : ℝ) + 1) / α) := by
  have hc : (1 : ℝ) ≤ (C : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 C
  have hr : 1 / α ≤ ((C : ℝ) + 1) / α := div_le_div_of_nonneg_right hc hα.le
  have hp : 4 / α ≤ (1 / α) ^ 3 := by
    have hh : 4 * α ^ 2 ≤ 1 := by nlinarith
    have hd : (4 : ℝ) ≤ 1 / α ^ 2 := (le_div_iff₀ (sq_pos_of_pos hα)).mpr hh
    calc
      4 / α ≤ (1 / α ^ 2) / α := div_le_div_of_nonneg_right hd hα.le
      _ = (1 / α) ^ 3 := by ring
  calc
    Real.log (4 / α) ≤ Real.log ((((C : ℝ) + 1) / α) ^ 3) := by
      apply Real.log_le_log (by positivity)
      exact hp.trans (pow_le_pow_left₀ (by positivity) hr 3)
    _ = _ := Real.log_pow _ _

theorem bitCutoff_le (C : ℕ) (I α : ℝ) (hI : 0 ≤ I) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) :
    (bitCutoff C I α : ℝ) ≤ 4 * trialScale I α + 4 * communicationCoefficient C * I / α + 10 := by
  have hN := (Nat.ceil_lt_add_one (trialScale_nonneg I α hI hα hα₁)).le
  have hM := (Nat.ceil_lt_add_one (show 0 ≤ 4 * communicationCoefficient C * I / α from
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (communicationCoefficient_nonneg C)) hI) hα.le)).le
  simp only [bitCutoff,trialCount,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  linarith

theorem bitCutoff_budget (C : ℕ) (I α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) (hI : α ^ 2 ≤ I) :
    (bitCutoff C I α : ℝ) ≤ compressionBudget compressionConstant I C α := by
  let L := Real.log (((C : ℝ) + 1) / α)
  let T := I * L / α ^ 2
  have hρ := acceptanceRate_pos
  have hI₀ : 0 ≤ I := (sq_nonneg α).trans hI
  have hL : 1 / 2 ≤ L := SmoothingCoupling.smoothingScale_half_le C α hα hα₁
  have hL₀ : 0 ≤ L := by linarith
  have hT : L ≤ T := by
    have hr : (1 : ℝ) ≤ I / α ^ 2 := (le_div_iff₀ (sq_pos_of_pos hα)).mpr (by simpa only [one_mul] using hI)
    have hh := mul_le_mul_of_nonneg_right hr hL₀
    calc
      L = 1 * L := (one_mul _).symm
      _ ≤ I / α ^ 2 * L := hh
      _ = T := by dsimp only [T]; ring
  have hT₀ : 0 ≤ T := hL₀.trans hT
  have hi : I / α ≤ 2 * T := by
    calc
      I / α = (I / α ^ 2) * α := by field_simp
      _ ≤ (I / α ^ 2) * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * T := by dsimp [T]; ring
  have hj : I * L / α ≤ T := by
    calc
      I * L / α = T * α := by dsimp [T]; field_simp
      _ ≤ T * 1 := mul_le_mul_of_nonneg_left (by linarith) hT₀
      _ = T := mul_one _
  have ht₁ : 128 * I / (acceptanceRate * α) ≤ 256 / acceptanceRate * T := by
    have hh := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 128 / acceptanceRate)
    convert hh using 1 <;> ring
  have ht₂ : 32 * Real.log (4 / α) / acceptanceRate ^ 2 ≤ 96 / acceptanceRate ^ 2 * T := by
    have hh := mul_le_mul_of_nonneg_left ((log_four_div_le C α hα hα₁).trans (show 3 * L ≤ 3 * T by linarith))
      (by positivity : 0 ≤ 32 / acceptanceRate ^ 2)
    convert hh using 1 <;> ring
  have hwidth := index_width_le C α hα hα₁
  have ht₃ : 4 * communicationCoefficient C * I / α ≤ 192 * Real.exp 4 / acceptanceRate * T := by
    have hh := mul_le_mul_of_nonneg_right hwidth (show 0 ≤ 32 * Real.exp 4 * I / (acceptanceRate * α) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hj (show 0 ≤ 192 * Real.exp 4 / acceptanceRate by positivity)
    dsimp only [communicationCoefficient]
    calc
      _ ≤ 192 * Real.exp 4 / acceptanceRate * (I * L / α) := by convert hh using 1 <;> (try dsimp only [L]) <;> ring
      _ ≤ _ := hh'
  have hcost := bitCutoff_le C I α hI₀ hα hα₁
  have he : 4 * trialScale I α = 128 * I / (acceptanceRate * α) + 32 * Real.log (4 / α) / acceptanceRate ^ 2 := by
    unfold trialScale
    ring
  rw [he] at hcost
  have hbudget : compressionBudget compressionConstant I C α = compressionConstant * T := by
    unfold compressionBudget T
    ring
  rw [hbudget]
  dsimp only [compressionConstant]
  nlinarith

end BBCR.LikelihoodFrontier
