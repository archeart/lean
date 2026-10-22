module

public import BBCR.TwoPartyRejection
public import BBCR.FiniteInformation
public import BBCR.FiniteCoupling

/-! Information charging for likelihood-excursion frontiers. The inverse
likelihood has mean one, so crossing a fixed log threshold costs a constant
amount of expected information. No reciprocal-logarithmic cutoff is used. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR

noncomputable def likelihoodPotential (z : ℝ) : ℝ := Real.exp (-z) - 1 + z

theorem likelihoodPotential_nonneg (z : ℝ) : 0 ≤ likelihoodPotential z := by
  have hh := Real.add_one_le_exp (-z)
  dsimp only [likelihoodPotential]
  linarith

theorem likelihoodPotential_quarter (z : ℝ) (hz : 1 ≤ |z|) : 1 / 4 ≤ likelihoodPotential z := by
  rcases le_total 0 z with hpos | hneg
  · have hz₁ : 1 ≤ z := by rwa [abs_of_nonneg hpos] at hz
    have ha : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
      linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
    have hb : Real.exp (-(1 / 2 : ℝ)) ≤ 1 := by
      exact (Real.exp_le_exp.mpr (by norm_num : -(1 / 2 : ℝ) ≤ 0)).trans_eq Real.exp_zero
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 / 2 - z))
      (Real.exp_pos (-(1 / 2 : ℝ))).le
    rw [← Real.exp_add, show -(1 / 2 : ℝ) + (1 / 2 - z) = -z by ring] at hh
    dsimp only [likelihoodPotential]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hz₁)]
  · have hz₁ : z ≤ -1 := by rw [abs_of_nonpos hneg] at hz; linarith
    have ha : (3 / 2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
      linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-z - 1 / 2))
      (Real.exp_pos (1 / 2 : ℝ)).le
    rw [← Real.exp_add, show (1 / 2 : ℝ) + (-z - 1 / 2) = -z by ring] at hh
    have hm := mul_le_mul_of_nonneg_right ha (show 0 ≤ -z - 1 / 2 + 1 by linarith)
    dsimp only [likelihoodPotential]
    linarith

namespace TwoPartyRejection

variable {A : Type*} [Fintype A]

theorem inverse_likelihood_mean (C P Q D : PMF A)
    (hC : ∀ x, 0 < mass C x) (hP : ∀ x, 0 < mass P x)
    (hfactor : ∀ x, mass P x * mass Q x = mass C x * mass D x) :
    (∑ x, mass D x * Real.exp (-Real.log (mass P x / mass C x))) = 1 := by
  calc
    _ = ∑ x, mass Q x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Real.exp_neg, Real.exp_log (div_pos (hP x) (hC x)), inv_div]
      rw [← mul_div_assoc]
      apply (div_eq_iff (hP x).ne').mpr
      nlinarith [hfactor x]
    _ = 1 := sum_mass Q

omit [Fintype A] in
theorem sum_log_likelihood (C P Q D : PMF A)
    (hC : ∀ x, 0 < mass C x) (hP : ∀ x, 0 < mass P x)
    (hQ : ∀ x, 0 < mass Q x) (_hD : ∀ x, 0 < mass D x)
    (hfactor : ∀ x, mass P x * mass Q x = mass C x * mass D x) (x : A) :
    Real.log (mass P x / mass C x) + Real.log (mass Q x / mass C x) =
      Real.log (mass D x / mass C x) := by
  rw [← Real.log_mul (div_pos (hP x) (hC x)).ne' (div_pos (hQ x) (hC x)).ne']
  congr 1
  field_simp [(hC x).ne']
  nlinarith [hfactor x]

/-- Expected information bounds the chance of a nonterminal likelihood
excursion by a constant factor. This replaces the `D/β` round charge. -/
theorem excursion_mass_le (C P Q D : PMF A)
    (hC : ∀ x, 0 < mass C x) (hP : ∀ x, 0 < mass P x)
    (hQ : ∀ x, 0 < mass Q x) (hD : ∀ x, 0 < mass D x)
    (hfactor : ∀ x, mass P x * mass Q x = mass C x * mass D x) :
    probability D (fun x ↦ 1 ≤ |Real.log (mass P x / mass C x)| ∨
      1 ≤ |Real.log (mass Q x / mass C x)|) ≤ 4 * divergence D C := by
  have hp := inverse_likelihood_mean C P Q D hC hP hfactor
  have hq := inverse_likelihood_mean C Q P D hC hQ (fun x ↦ by rw [mul_comm]; exact hfactor x)
  have hpoint (x : A) :
      (if 1 ≤ |Real.log (mass P x / mass C x)| ∨ 1 ≤ |Real.log (mass Q x / mass C x)|
        then mass D x else 0) ≤
      4 * mass D x * (likelihoodPotential (Real.log (mass P x / mass C x)) +
        likelihoodPotential (Real.log (mass Q x / mass C x))) := by
    split_ifs with hx
    · have hsum : 1 / 4 ≤ likelihoodPotential (Real.log (mass P x / mass C x)) +
          likelihoodPotential (Real.log (mass Q x / mass C x)) := by
        rcases hx with hx | hx
        · linarith [likelihoodPotential_quarter _ hx, likelihoodPotential_nonneg (Real.log (mass Q x / mass C x))]
        · linarith [likelihoodPotential_quarter _ hx, likelihoodPotential_nonneg (Real.log (mass P x / mass C x))]
      nlinarith [mul_le_mul_of_nonneg_left hsum (mass_nonneg D x)]
    · exact mul_nonneg (mul_nonneg (by norm_num) (mass_nonneg D x))
        (add_nonneg (likelihoodPotential_nonneg _) (likelihoodPotential_nonneg _))
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) ↦ hpoint x)
  have he : (∑ x, 4 * mass D x * (likelihoodPotential (Real.log (mass P x / mass C x)) +
      likelihoodPotential (Real.log (mass Q x / mass C x)))) = 4 * divergence D C := by
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    have hl : (∑ x, mass D x * Real.log (mass P x / mass C x)) +
        (∑ x, mass D x * Real.log (mass Q x / mass C x)) = divergence D C := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [← mul_add, sum_log_likelihood C P Q D hC hP hQ hD hfactor x]
    simp only [likelihoodPotential, mul_add, mul_sub, mul_one, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hp, hq, sum_mass]
    linarith
  have hevent : probability D (fun x ↦ 1 ≤ |Real.log (mass P x / mass C x)| ∨
      1 ≤ |Real.log (mass Q x / mass C x)|) =
      ∑ x, if 1 ≤ |Real.log (mass P x / mass C x)| ∨ 1 ≤ |Real.log (mass Q x / mass C x)|
        then mass D x else 0 := by
    unfold probability
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl
  rw [hevent]
  exact hs.trans_eq he

theorem exact_rate (C P Q D : PMF A) (t : ℝ) (ht : 0 < t)
    (hC : ∀ x, 0 < mass C x)
    (hfactor : ∀ x, mass P x * mass Q x = mass C x * mass D x)
    (hP : ∀ x, mass P x ≤ t * mass C x) (hQ : ∀ x, mass Q x ≤ t * mass C x) :
    Rejection.rate C (acceptWeight C P Q t) = 1 / t ^ 2 := by
  have he (x : A) : acceptWeight C P Q t x = idealWeight C P Q t x := by
    unfold acceptWeight idealWeight
    rw [min_eq_right ((div_le_one (mul_pos ht (hC x))).mpr (hP x)),
      min_eq_right ((div_le_one (mul_pos ht (hC x))).mpr (hQ x))]
  simp only [Rejection.rate, he, ideal_identity C P Q D t ht hC hfactor,
    ← Finset.mul_sum, sum_mass, mul_one]

theorem exact_accepted (C P Q D : PMF A) (t : ℝ) (ht : 0 < t)
    (hC : ∀ x, 0 < mass C x)
    (hfactor : ∀ x, mass P x * mass Q x = mass C x * mass D x)
    (hP : ∀ x, mass P x ≤ t * mass C x) (hQ : ∀ x, mass Q x ≤ t * mass C x) :
    ∃ hr : 0 < Rejection.rate C (acceptWeight C P Q t),
      Rejection.accepted C (acceptWeight C P Q t) (accept_nonneg C P Q t ht) hr = D := by
  have hr := exact_rate C P Q D t ht hC hfactor hP hQ
  have hr₀ : 0 < Rejection.rate C (acceptWeight C P Q t) := by rw [hr]; positivity
  refine ⟨hr₀, ?_⟩
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change mass _ x = mass D x
  rw [Rejection.mass_accepted, hr]
  have he : acceptWeight C P Q t x = idealWeight C P Q t x := by
    unfold acceptWeight idealWeight
    rw [min_eq_right ((div_le_one (mul_pos ht (hC x))).mpr (hP x)),
      min_eq_right ((div_le_one (mul_pos ht (hC x))).mpr (hQ x))]
  rw [he, ideal_identity C P Q D t ht hC hfactor]
  field_simp

end TwoPartyRejection

namespace Rejection

variable {A : Type*} [Fintype A]

theorem expect_attempt (p : PMF A) (a : A → ℝ) (ha₀ : ∀ x, 0 ≤ a x) (ha₁ : ∀ x, a x ≤ 1)
    (hr : 0 < rate p a) (g : Option A → ℝ) :
    (∑ o, mass (attempt p a ha₀ ha₁) o * g o) =
      (1 - rate p a) * g none + rate p a * ∑ x, mass (accepted p a ha₀ hr) x * g (some x) := by
  rw [Fintype.sum_option, mass_attempt_none, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [mass_attempt_some, mass_accepted]
  field_simp

end Rejection
end BBCR
