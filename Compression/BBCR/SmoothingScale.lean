module

public import BBCR.SmoothingParameters

/-! With a reciprocal-logarithmic bias, the information-controlled smoothing
has at most cubic logarithmic communication inflation. The consistency of the
scale constant is checked in SmoothingLogBudget; smooth compression remains open. -/

@[expose] public section

open Disjointness

namespace BBCR.SmoothingCoupling

noncomputable def smoothingScale (C : ℕ) (α : ℝ) : ℝ :=
  Real.log (((C : ℝ) + 1) / α)

noncomputable def reciprocalBias (C : ℕ) (α k : ℝ) : ℝ :=
  1 / (4 * k * smoothingScale C α)

theorem smoothingScale_half_le (C : ℕ) (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) :
    1 / 2 ≤ smoothingScale C α := by
  have htwo : 2 ≤ ((C : ℝ) + 1) / α := by
    apply (le_div_iff₀ hα).mpr
    nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C]
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo
  dsimp only [smoothingScale]
  norm_num at hh
  linarith

theorem reciprocalBias_mem (C : ℕ) (α k : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1 / 2) (hk : 1 ≤ k) :
    0 < reciprocalBias C α k ∧ reciprocalBias C α k ≤ 1 / 2 := by
  have hL := smoothingScale_half_le C α hα hα₁
  have hL₀ : 0 < smoothingScale C α := by linarith
  have hk₀ : 0 < k := by linarith
  have hd : 0 < 4 * k * smoothingScale C α := by positivity
  constructor
  · exact div_pos (by norm_num) hd
  · apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_right hk hL₀.le
    nlinarith

/-- An explicit cubic logarithmic block bound, uniform over `C=0` and the
entire final error range. The scale parameter `k` is still arbitrary. -/
theorem informationBlockSize_polylog_bound (C : ℕ) (α k : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1 / 2) (hk : 1 ≤ k) :
    (informationBlockSize C α (reciprocalBias C α k) : ℝ) ≤
      544 * k ^ 3 * smoothingScale C α ^ 3 := by
  let L := smoothingScale C α
  let β := reciprocalBias C α k
  have hL : 1 / 2 ≤ L := smoothingScale_half_le C α hα hα₁
  have hL₀ : 0 < L := by linarith
  have hk₀ : 0 < k := by linarith
  have hβ := reciprocalBias_mem C α k hα hα₁ hk
  have hα₂ : α ≤ 1 := by linarith
  have hu := informationBlockSize_log_bound C α β hα hα₂ hβ.1 hβ.2
  have hD : Real.log (((C : ℝ) + 1) / (α * β)) =
      L + Real.log 4 + Real.log k + Real.log L := by
    have he : ((C : ℝ) + 1) / (α * β) = (((C : ℝ) + 1) / α) * (4 * k * L) := by
      dsimp only [β, reciprocalBias, L]
      field_simp
    rw [he, Real.log_mul (div_ne_zero (by positivity) hα.ne') (by positivity),
      Real.log_mul (by positivity : 4 * k ≠ 0) hL₀.ne',
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hk₀.ne']
    change L + (Real.log 4 + Real.log k + Real.log L) = _
    ring
  have hlog4 : Real.log 4 ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at hh ⊢
    exact hh
  have hlogk : Real.log k ≤ k := Real.log_le_self hk₀.le
  have hlogL : Real.log L ≤ L := Real.log_le_self hL₀.le
  have hmul : L ≤ k * L := by nlinarith [mul_nonneg (sub_nonneg.mpr hk) hL₀.le]
  have hkL : k ≤ 2 * (k * L) := by nlinarith [mul_le_mul_of_nonneg_left hL hk₀.le]
  have hone : 1 ≤ 2 * (k * L) := by linarith
  have hn : 3 * Real.log (((C : ℝ) + 1) / (α * β)) + 2 ≤ 34 * k * L := by
    rw [hD]
    linarith
  have hinv : (β ^ 2)⁻¹ = (4 * k * L) ^ 2 := by
    dsimp only [β, reciprocalBias, L]
    field_simp
  rw [div_eq_mul_inv, hinv] at hu
  calc
    _ ≤ (3 * Real.log (((C : ℝ) + 1) / (α * β)) + 2) * (4 * k * L) ^ 2 := hu
    _ ≤ (34 * k * L) * (4 * k * L) ^ 2 :=
      mul_le_mul_of_nonneg_right hn (sq_nonneg _)
    _ = _ := by dsimp only [L]; ring

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R]
  [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

/-- The parameterized actual simulator has the stronger information accuracy
and only cubic logarithmic communication inflation. This is smoothing, not the
information-dependent communication bound of Theorem 2.2. -/
theorem smoothing_at_scale (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (α k : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) (hk : 1 ≤ k) :
    let β := reciprocalBias p.cost α k
    let hb := reciprocalBias_mem p.cost α k hα hα₁ hk
    let s := informationSimulator p α β hb.1.le hb.2
    s.Simulates μ α ∧ Smooth s.protocol β ∧
      externalInformation s.protocol μ ≤ externalInformation p μ + α ^ 2 ∧
      (s.cost : ℝ) ≤ 544 * k ^ 3 * smoothingScale p.cost α ^ 3 * p.cost := by
  let β := reciprocalBias p.cost α k
  have hb := reciprocalBias_mem p.cost α k hα hα₁ hk
  have hα₂ : α ≤ 1 := by linarith
  obtain ⟨hc,hs,hsm,hi⟩ := smoothing_at_information_error p μ α β hα hα₂ hb.1 hb.2
  have hc' : ((informationSimulator p α β hb.1.le hb.2).cost : ℝ) ≤
      (informationBlockSize p.cost α β : ℝ) * p.cost := by exact_mod_cast hc
  exact ⟨hs,hsm,hi,hc'.trans (mul_le_mul_of_nonneg_right
    (informationBlockSize_polylog_bound p.cost α k hα hα₁ hk) (Nat.cast_nonneg _))⟩

end BBCR.SmoothingCoupling
