module

public import BBCR.SmoothingScale

/-! The reciprocal-logarithmic smoothness requirement can refer to the actual
smoothed communication bound. Constants here are deliberately nonoptimal. -/

@[expose] public section

open Disjointness

namespace BBCR.SmoothingCoupling

/-- Cubic logarithmic communication inflation changes the communication
logarithm by only a constant factor, uniformly in the original cost. -/
theorem smoothingScale_inflation (C Q : ℕ) (α k : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1 / 2) (hk : 1 ≤ k)
    (hQ : (Q : ℝ) ≤ 544 * k ^ 3 * smoothingScale C α ^ 3 * C) :
    smoothingScale Q α ≤ (1092 + 6 * Real.log k) * smoothingScale C α := by
  let L := smoothingScale C α
  have hL : 1 / 2 ≤ L := smoothingScale_half_le C α hα hα₁
  have hL₀ : 0 < L := by linarith
  have hk₀ : 0 < k := by linarith
  have hk3 : 1 ≤ k ^ 3 := one_le_pow₀ hk
  have hcube : L ^ 3 ≤ (L + 1) ^ 3 := by gcongr; linarith
  have hlarge : 1 ≤ k ^ 3 * (L + 1) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hk3 (by positivity : 0 ≤ (L + 1) ^ 3)
    have h' : 1 ≤ (L + 1) ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  have hcoef : 544 * k ^ 3 * L ^ 3 + 1 ≤ 545 * k ^ 3 * (L + 1) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hcube (by positivity : 0 ≤ 544 * k ^ 3)
    nlinarith
  have hnum : (Q : ℝ) + 1 ≤ (545 * k ^ 3 * (L + 1) ^ 3) * ((C : ℝ) + 1) := by
    calc
      _ ≤ 544 * k ^ 3 * L ^ 3 * C + 1 := add_le_add hQ le_rfl
      _ ≤ (544 * k ^ 3 * L ^ 3 + 1) * ((C : ℝ) + 1) := by
        nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C,
          show 0 ≤ 544 * k ^ 3 * L ^ 3 from by positivity]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hratio : ((Q : ℝ) + 1) / α ≤
      (545 * k ^ 3 * (L + 1) ^ 3) * (((C : ℝ) + 1) / α) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hnum hα.le
  have hlog := Real.log_le_log (by positivity : 0 < ((Q : ℝ) + 1) / α) hratio
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity : 545 * k ^ 3 ≠ 0) (by positivity : (L + 1) ^ 3 ≠ 0),
    Real.log_mul (by norm_num : (545 : ℝ) ≠ 0) (pow_ne_zero 3 hk₀.ne'),
    Real.log_pow, Real.log_pow] at hlog
  have hlog545 : Real.log 545 ≤ 544 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 545)
    norm_num at hh ⊢
    exact hh
  have hlogL : Real.log (L + 1) ≤ L := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < L + 1)
    linarith
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hmul := mul_le_mul_of_nonneg_left hL hlogk
  change Real.log (((Q : ℝ) + 1) / α) ≤ _
  change Real.log (((Q : ℝ) + 1) / α) ≤
    Real.log 545 + (3 : ℝ) * Real.log k + (3 : ℝ) * Real.log (L + 1) + L at hlog
  nlinarith

theorem smoothing_scale_constant (κ : ℝ) (hκ : 1 ≤ κ) :
    let k := (32 * κ) ^ 2
    1 ≤ k ∧ κ * (1092 + 6 * Real.log k) ≤ 4 * k := by
  have hκ₀ : 0 < κ := by linarith
  have hlog : Real.log ((32 * κ) ^ 2) ≤ 64 * κ := by
    rw [Real.log_pow]
    norm_num
    have hh := Real.log_le_self (by positivity : 0 ≤ 32 * κ)
    linarith
  have hh := mul_le_mul_of_nonneg_left hlog hκ₀.le
  constructor
  · nlinarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hκ) hκ₀.le]

/-- The bias is small enough for a smooth-compression condition involving the
smoothed communication, rather than only the original communication. -/
theorem reciprocalBias_le_inflated_scale (C Q : ℕ) (α κ : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1 / 2) (hκ : 1 ≤ κ)
    (hQ : (Q : ℝ) ≤ 544 * ((32 * κ) ^ 2) ^ 3 * smoothingScale C α ^ 3 * C) :
    reciprocalBias C α ((32 * κ) ^ 2) ≤ 1 / (κ * smoothingScale Q α) := by
  let k := (32 * κ) ^ 2
  obtain ⟨hk,hkbound⟩ := smoothing_scale_constant κ hκ
  have hL := smoothingScale_half_le C α hα hα₁
  have hQlog := smoothingScale_half_le Q α hα hα₁
  have hL₀ : 0 < smoothingScale C α := by linarith
  have hQ₀ : 0 < smoothingScale Q α := by linarith
  have hκ₀ : 0 < κ := by linarith
  have hk₀ : 0 < k := by dsimp only [k]; positivity
  have hlog := mul_le_mul_of_nonneg_left
    (smoothingScale_inflation C Q α k hα hα₁ hk hQ) hκ₀.le
  have hconst := mul_le_mul_of_nonneg_right hkbound hL₀.le
  unfold reciprocalBias
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * k * smoothingScale C α)
    (by positivity : 0 < κ * smoothingScale Q α)).mpr
  nlinarith

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R]
  [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

/-- Concrete preprocessing for an eventual smooth-compression constant `κ`.
Smoothness refers to this simulator's own cost, information is at most twice
the original, and its cost logarithm stays within a fixed original-log factor.
The smooth compressor itself is not assumed or constructed by this theorem. -/
theorem smoothing_ready_for_compression (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (α κ : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) (hκ : 1 ≤ κ)
    (hinfo : α ^ 2 ≤ externalInformation p μ) :
    let k := (32 * κ) ^ 2
    let β := reciprocalBias p.cost α k
    let hb := reciprocalBias_mem p.cost α k hα hα₁ (smoothing_scale_constant κ hκ).1
    let s := informationSimulator p α β hb.1.le hb.2
    s.Simulates μ α ∧ Smooth s.protocol (1 / (κ * smoothingScale s.cost α)) ∧
      externalInformation s.protocol μ ≤ 2 * externalInformation p μ ∧
      (s.cost : ℝ) ≤ 544 * k ^ 3 * smoothingScale p.cost α ^ 3 * p.cost ∧
      smoothingScale s.cost α ≤ 1476 * κ * smoothingScale p.cost α := by
  let k := (32 * κ) ^ 2
  let β := reciprocalBias p.cost α k
  have hk := (smoothing_scale_constant κ hκ).1
  have hb := reciprocalBias_mem p.cost α k hα hα₁ hk
  let s := informationSimulator p α β hb.1.le hb.2
  obtain ⟨hs,hsm,_,hc⟩ := smoothing_at_scale p μ α k hα hα₁ hk
  have hβ : β ≤ 1 / (κ * smoothingScale s.cost α) :=
    reciprocalBias_le_inflated_scale p.cost s.cost α κ hα hα₁ hκ hc
  have hα₂ : α ≤ 1 := by linarith
  have hi := smoothing_information_le_twice p μ α β hα hα₂ hb.1 hb.2 hinfo
  have hκ₀ : 0 < κ := by linarith
  have hlogk : Real.log k ≤ 64 * κ := by
    dsimp only [k]
    rw [Real.log_pow]
    norm_num
    have hh := Real.log_le_self (by positivity : 0 ≤ 32 * κ)
    linarith
  have hcoef : 1092 + 6 * Real.log k ≤ 1476 * κ := by linarith
  have hL : 0 ≤ smoothingScale p.cost α := (smoothingScale_half_le p.cost α hα hα₁).trans' (by norm_num)
  have hlog := (smoothingScale_inflation p.cost s.cost α k hα hα₁ hk hc).trans
    (mul_le_mul_of_nonneg_right hcoef hL)
  refine ⟨hs,?_,hi,hc,?_⟩
  · intro r x y bits who hwho hpos
    obtain ⟨hl,hu⟩ := hsm r x y bits who hwho hpos
    constructor <;> linarith
  · simpa only [mul_assoc] using hlog

end BBCR.SmoothingCoupling
