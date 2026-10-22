module

public import BBCR.BoundedRejection

/-! Algebraic core of BBCR's two-party rejection step. FrontierRejection proves
the factorization and positivity hypotheses for actual protocol frontiers.
FrontierLikelihood proves the likelihood-ratio concentration bound, and
FrontierSampling supplies explicit parameter choices. -/

@[expose] public section

open Disjointness.Hellinger

namespace BBCR.TwoPartyRejection

variable {A : Type*} [Fintype A]

noncomputable def acceptWeight (C P Q : PMF A) (t : ℝ) (x : A) : ℝ :=
  min 1 (mass P x / (t * mass C x)) * min 1 (mass Q x / (t * mass C x))

noncomputable def idealWeight (C P Q : PMF A) (t : ℝ) (x : A) : ℝ :=
  (mass P x / (t * mass C x)) * (mass Q x / (t * mass C x))

omit [Fintype A] in
theorem accept_nonneg (C P Q : PMF A) (t : ℝ) (ht : 0 < t) (x : A) :
    0 ≤ acceptWeight C P Q t x :=
  mul_nonneg (le_min (by norm_num) (div_nonneg (mass_nonneg P x) (mul_nonneg ht.le (mass_nonneg C x))))
    (le_min (by norm_num) (div_nonneg (mass_nonneg Q x) (mul_nonneg ht.le (mass_nonneg C x))))

omit [Fintype A] in
theorem accept_le_one (C P Q : PMF A) (t : ℝ) (ht : 0 < t) (x : A) :
    acceptWeight C P Q t x ≤ 1 := by
  have hq : 0 ≤ min 1 (mass Q x / (t * mass C x)) :=
    le_min (by norm_num) (div_nonneg (mass_nonneg Q x) (mul_nonneg ht.le (mass_nonneg C x)))
  exact (mul_le_mul (min_le_left _ _) (min_le_left _ _) hq (by norm_num)).trans_eq (one_mul 1)

omit [Fintype A] in
theorem accept_le_ideal (C P Q : PMF A) (t : ℝ) (ht : 0 < t) (x : A) :
    acceptWeight C P Q t x ≤ idealWeight C P Q t x := by
  apply mul_le_mul (min_le_right _ _) (min_le_right _ _)
  · exact le_min (by norm_num) (div_nonneg (mass_nonneg Q x) (mul_nonneg ht.le (mass_nonneg C x)))
  · exact div_nonneg (mass_nonneg P x) (mul_nonneg ht.le (mass_nonneg C x))

omit [Fintype A] in
/-- Cross-multiplied version of the likelihood identity (8.5) implies that the
unclipped rejection rule has exactly the target law before normalization. -/
theorem ideal_identity (C P Q D : PMF A) (t : ℝ) (ht : 0 < t)
    (hC : ∀ x, 0 < mass C x)
    (hfactor : ∀ x, mass P x * mass Q x = mass C x * mass D x) (x : A) :
    mass C x * idealWeight C P Q t x = (1 / t ^ 2) * mass D x := by
  unfold idealWeight
  field_simp [ht.ne', (hC x).ne']
  nlinarith [hfactor x]

noncomputable def badSet (C P Q : PMF A) (t : ℝ) : Finset A :=
  Finset.univ.filter fun x ↦ t * mass C x < mass P x ∨ t * mass C x < mass Q x

noncomputable def badMass (C P Q D : PMF A) (t : ℝ) : ℝ :=
  ∑ x ∈ badSet C P Q t, mass D x

theorem badMass_nonneg (C P Q D : PMF A) (t : ℝ) : 0 ≤ badMass C P Q D t :=
  Finset.sum_nonneg fun x _ ↦ mass_nonneg D x

theorem accept_eq_ideal_off_bad (C P Q : PMF A) (t : ℝ) (ht : 0 < t)
    (hC : ∀ x, 0 < mass C x) (x : A) (hx : x ∉ badSet C P Q t) :
    acceptWeight C P Q t x = idealWeight C P Q t x := by
  classical
  have hh : mass P x ≤ t * mass C x ∧ mass Q x ≤ t * mass C x := by
    simpa only [badSet, Finset.mem_filter, Finset.mem_univ, true_and,
      not_or, not_lt] using hx
  unfold acceptWeight idealWeight
  rw [min_eq_right ((div_le_one (mul_pos ht (hC x))).mpr hh.1),
    min_eq_right ((div_le_one (mul_pos ht (hC x))).mpr hh.2)]

/-- Acceptance probability is at least `(1-δ)/t²`, where δ is the target
probability of either player's likelihood ratio exceeding the clipping level. -/
theorem rate_lower (C P Q D : PMF A) (t : ℝ) (ht : 0 < t)
    (hC : ∀ x, 0 < mass C x)
    (hfactor : ∀ x, mass P x * mass Q x = mass C x * mass D x) :
    (1 / t ^ 2) * (1 - badMass C P Q D t) ≤ Rejection.rate C (acceptWeight C P Q t) := by
  exact Rejection.rate_ge_of_exception C D (acceptWeight C P Q t) (idealWeight C P Q t)
    (1 / t ^ 2) (accept_nonneg C P Q t ht) (ideal_identity C P Q D t ht hC hfactor)
    (badSet C P Q t) (accept_eq_ideal_off_bad C P Q t ht hC)

theorem rate_pos (C P Q D : PMF A) (t : ℝ) (ht : 0 < t)
    (hC : ∀ x, 0 < mass C x)
    (hfactor : ∀ x, mass P x * mass Q x = mass C x * mass D x)
    (hbad : badMass C P Q D t < 1) : 0 < Rejection.rate C (acceptWeight C P Q t) :=
  lt_of_lt_of_le (mul_pos (by positivity) (sub_pos.mpr hbad)) (rate_lower C P Q D t ht hC hfactor)

/-- The algebraic distortion estimate used after the likelihood-ratio tail
bound in Claim 8.9. It is not a proof of that concentration bound. -/
theorem accepted_close (C P Q D : PMF A) (t : ℝ) (ht : 0 < t)
    (hC : ∀ x, 0 < mass C x)
    (hfactor : ∀ x, mass P x * mass Q x = mass C x * mass D x)
    (hbad : badMass C P Q D t < 1) :
    variation (Rejection.accepted C (acceptWeight C P Q t) (accept_nonneg C P Q t ht)
      (rate_pos C P Q D t ht hC hfactor hbad)) D ≤ badMass C P Q D t := by
  exact Rejection.accepted_close C D (acceptWeight C P Q t) (idealWeight C P Q t)
    (1 / t ^ 2) (badMass C P Q D t) (by positivity) (badMass_nonneg C P Q D t) hbad
    (accept_nonneg C P Q t ht) (accept_le_ideal C P Q t ht)
    (ideal_identity C P Q D t ht hC hfactor) (rate_lower C P Q D t ht hC hfactor)

/-- Pointwise domination is needed when rounds are composed: a small TV bound
alone does not control the cost of paths favored by the simulated law. -/
theorem accepted_mass_le (C P Q D : PMF A) (t : ℝ) (ht : 0 < t)
    (hC : ∀ x, 0 < mass C x)
    (hfactor : ∀ x, mass P x * mass Q x = mass C x * mass D x)
    (hbad : badMass C P Q D t < 1) (x : A) :
    mass (Rejection.accepted C (acceptWeight C P Q t) (accept_nonneg C P Q t ht)
      (rate_pos C P Q D t ht hC hfactor hbad)) x ≤ mass D x / (1 - badMass C P Q D t) := by
  have hr := rate_pos C P Q D t ht hC hfactor hbad
  have hl := rate_lower C P Q D t ht hC hfactor
  have hn := mul_le_mul_of_nonneg_left (accept_le_ideal C P Q t ht x) (mass_nonneg C x)
  rw [ideal_identity C P Q D t ht hC hfactor x] at hn
  rw [Rejection.mass_accepted]
  apply (div_le_iff₀ hr).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hbad)).mpr
  have hh := mul_le_mul_of_nonneg_left hl (mass_nonneg D x)
  have hh' := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hbad.le)
  nlinarith

end BBCR.TwoPartyRejection
