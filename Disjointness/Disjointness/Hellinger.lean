module

public import Disjointness.ProbabilityTools
public import Mathlib.Analysis.Real.Sqrt

/-! Finite squared Hellinger distance, total variation, and the information comparison. -/

@[expose] public section

open scoped ENNReal
open Real

namespace Disjointness.Hellinger

variable {A : Type*} [Fintype A]

noncomputable def mass (p : PMF A) (a : A) : ℝ := (p a).toReal

omit [Fintype A] in
theorem mass_nonneg (p : PMF A) (a : A) : 0 ≤ mass p a := ENNReal.toReal_nonneg

@[simp] theorem sum_mass (p : PMF A) : ∑ a, mass p a = 1 := by
  simp only [mass]
  rw [← ENNReal.toReal_sum (fun a _ ↦ p.apply_ne_top a), FiniteLaw.sum_pmf]
  rfl

/-- Squared Hellinger distance, with the factor `1/2`. -/
noncomputable def sqDist (p q : PMF A) : ℝ :=
  (∑ a, (sqrt (mass p a) - sqrt (mass q a)) ^ 2) / 2

theorem sqDist_nonneg (p q : PMF A) : 0 ≤ sqDist p q := by
  unfold sqDist
  positivity

theorem sqDist_comm (p q : PMF A) : sqDist p q = sqDist q p := by
  simp only [sqDist, sub_sq_comm]

theorem sqDist_eq_one_sub_affinity (p q : PMF A) :
    sqDist p q = 1 - ∑ a, sqrt (mass p a) * sqrt (mass q a) := by
  have h (a : A) : (sqrt (mass p a) - sqrt (mass q a)) ^ 2 =
      mass p a + mass q a - 2 * (sqrt (mass p a) * sqrt (mass q a)) := by
    nlinarith [sq_sqrt (mass_nonneg p a), sq_sqrt (mass_nonneg q a)]
  simp_rw [sqDist, h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_mass]
  ring

/-- The squared triangle inequality loses a factor of two. -/
theorem sqDist_triangle (p q r : PMF A) : sqDist p r ≤ 2 * sqDist p q + 2 * sqDist q r := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    show (sqrt (mass p a) - sqrt (mass r a)) ^ 2 ≤
      2 * (sqrt (mass p a) - sqrt (mass q a)) ^ 2 +
      2 * (sqrt (mass q a) - sqrt (mass r a)) ^ 2 by
        nlinarith [sq_nonneg (sqrt (mass p a) + sqrt (mass r a) - 2 * sqrt (mass q a))])
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  unfold sqDist
  linarith

/-- The rectangle identity implies Hellinger cut-and-paste. -/
theorem cut_and_paste (p00 p01 p10 p11 : PMF A)
    (h : ∀ a, mass p00 a * mass p11 a = mass p01 a * mass p10 a) :
    sqDist p00 p11 = sqDist p01 p10 := by
  rw [sqDist_eq_one_sub_affinity, sqDist_eq_one_sub_affinity]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← sqrt_mul (mass_nonneg p00 a), h a, sqrt_mul (mass_nonneg p01 a)]

noncomputable def variation (p q : PMF A) : ℝ := (∑ a, |mass p a - mass q a|) / 2

theorem variation_nonneg (p q : PMF A) : 0 ≤ variation p q := by
  unfold variation
  positivity

/-- The total-variation/Hellinger estimate remains useful at error `1/3`. -/
theorem variation_sq_le (p q : PMF A) : variation p q ^ 2 ≤ 2 * sqDist p q := by
  let f := fun a ↦ |sqrt (mass p a) - sqrt (mass q a)|
  let g := fun a ↦ sqrt (mass p a) + sqrt (mass q a)
  have hfg (a : A) : |mass p a - mass q a| = f a * g a := by
    have h : mass p a - mass q a =
        (sqrt (mass p a) - sqrt (mass q a)) * g a := by
      dsimp [g]
      nlinarith [sq_sqrt (mass_nonneg p a), sq_sqrt (mass_nonneg q a)]
    rw [h, abs_mul, abs_of_nonneg (show 0 ≤ g a by dsimp [g]; positivity)]
  have hg : ∑ a, g a ^ 2 ≤ 4 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
      show g a ^ 2 ≤ 2 * mass p a + 2 * mass q a by
        dsimp [g]
        nlinarith [sq_sqrt (mass_nonneg p a), sq_sqrt (mass_nonneg q a),
          sq_nonneg (sqrt (mass p a) - sqrt (mass q a))])
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_mass, mul_one, show (2 : ℝ) + 2 = 4 by norm_num] using h
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hm := mul_le_mul_of_nonneg_left hg (show 0 ≤ ∑ a, f a ^ 2 from
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  simp only [f, sq_abs] at hc hm
  unfold variation sqDist
  simp_rw [hfg]
  nlinarith

/-- A decision event cannot distinguish two laws by more than total variation. -/
theorem event_difference_le (p q : PMF A) (s : Finset A) :
    |(∑ a ∈ s, mass p a) - ∑ a ∈ s, mass q a| ≤ variation p q := by
  classical
  let f := fun a ↦ mass p a - mass q a
  have hz : ∑ a, f a = 0 := by simp [f, Finset.sum_sub_distrib]
  have hsum : (∑ a ∈ s, f a) + ∑ a ∈ sᶜ, f a = 0 := by
    rw [Finset.sum_add_sum_compl, hz]
  have h₁ := Finset.abs_sum_le_sum_abs f s
  have h₂ := Finset.abs_sum_le_sum_abs f sᶜ
  have habs : |∑ a ∈ sᶜ, f a| = |∑ a ∈ s, f a| := by
    have h : (∑ a ∈ sᶜ, f a) = -(∑ a ∈ s, f a) := by linarith
    rw [h, abs_neg]
  rw [habs] at h₂
  have ha : (∑ a ∈ s, |f a|) + ∑ a ∈ sᶜ, |f a| = ∑ a, |f a| :=
    Finset.sum_add_sum_compl s _
  change |(∑ a ∈ s, mass p a) - ∑ a ∈ s, mass q a| ≤ (∑ a, |f a|) / 2
  rw [← Finset.sum_sub_distrib]
  change |∑ a ∈ s, f a| ≤ _
  linarith

/-- Scalar KL dominates the squared difference of square roots, with the
normalization correction explicit. The absolute-continuity premise is essential. -/
theorem sqrt_sub_sq_le_log {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) :
    (sqrt a - sqrt b) ^ 2 ≤ a * log (a / b) - a + b := by
  by_cases ha0 : a = 0
  · simp [ha0, sq_sqrt hb]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm (fun h ↦ ha0 (hab h)))
  have h := log_le_sub_one_of_pos (div_pos (sqrt_pos.mpr hbp) (sqrt_pos.mpr hap))
  rw [log_div (ne_of_gt (sqrt_pos.mpr hbp)) (ne_of_gt (sqrt_pos.mpr hap)),
    log_sqrt hb, log_sqrt ha] at h
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * a by positivity)
  have hs : a * (sqrt b / sqrt a) = sqrt a * sqrt b := by
    rw [← mul_div_assoc]
    apply (div_eq_iff (ne_of_gt (sqrt_pos.mpr hap))).mpr
    nlinarith [congrArg (fun x : ℝ ↦ x * sqrt b) (sq_sqrt ha)]
  rw [log_div ha0 (ne_of_gt hbp)]
  nlinarith [sq_sqrt ha, sq_sqrt hb]

/-- Quantitative concavity of `-x log x`, valid even at zero masses. -/
theorem sqrt_gap_le_entropy_gap {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (sqrt a - sqrt b) ^ 2 ≤
      4 * (negMulLog ((a + b) / 2) - (negMulLog a + negMulLog b) / 2) := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, negMulLog]
  let m := (a + b) / 2
  have hm : 0 < m := by dsimp [m]; positivity
  have ht (x : ℝ) : x * log (x / m) = x * log x - x * log m := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [log_div hx (ne_of_gt hm)]; ring
  have h₁ := sqrt_sub_sq_le_log ha hm.le (fun h ↦ (ne_of_gt hm h).elim)
  have h₂ := sqrt_sub_sq_le_log hb hm.le (fun h ↦ (ne_of_gt hm h).elim)
  rw [ht] at h₁ h₂
  change (sqrt a - sqrt b) ^ 2 ≤ 4 * (negMulLog m - (negMulLog a + negMulLog b) / 2)
  unfold negMulLog
  have he : 2 * m = a + b := by dsimp [m]; ring
  nlinarith [sq_nonneg (sqrt a + sqrt b - 2 * sqrt m),
    congrArg (fun x : ℝ ↦ x * log m) he]

/-- Finite Jensen--Shannon expression in nats; `BinaryInformation.lean` identifies
it with PFR mutual information for a fair binary selector. -/
noncomputable def jensenShannon (p q : PMF A) : ℝ :=
  ∑ a, (negMulLog ((mass p a + mass q a) / 2) -
    (negMulLog (mass p a) + negMulLog (mass q a)) / 2)

theorem sqDist_le_two_jensenShannon (p q : PMF A) : sqDist p q ≤ 2 * jensenShannon p q := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    sqrt_gap_le_entropy_gap (mass_nonneg p a) (mass_nonneg q a))
  rw [← Finset.mul_sum] at h
  unfold sqDist jensenShannon
  linarith

end Disjointness.Hellinger
