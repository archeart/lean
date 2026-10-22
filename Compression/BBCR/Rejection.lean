module

public import Disjointness.Hellinger

/-! Normalized finite rejection laws, and quantitative bounds for clipping.
These laws are not yet an implementation of the two-party compression protocol. -/

@[expose] public section

open Disjointness.Hellinger

namespace BBCR.Rejection

variable {A : Type*} [Fintype A]

noncomputable def rate (p : PMF A) (a : A → ℝ) : ℝ := ∑ x, mass p x * a x

theorem rate_nonneg (p : PMF A) (a : A → ℝ) (ha : ∀ x, 0 ≤ a x) :
    0 ≤ rate p a := Finset.sum_nonneg fun x _ ↦ mul_nonneg (mass_nonneg p x) (ha x)

theorem rate_le_one (p : PMF A) (a : A → ℝ) (ha : ∀ x, a x ≤ 1) :
    rate p a ≤ 1 := by
  calc
    _ ≤ ∑ x, mass p x * 1 := Finset.sum_le_sum fun x _ ↦
      mul_le_mul_of_nonneg_left (ha x) (mass_nonneg p x)
    _ = 1 := by simp [sum_mass]

/-- Law of the accepted sample, when the acceptance probability is positive.
The normalization is proved from the actual proposal and acceptance weights. -/
noncomputable def accepted (p : PMF A) (a : A → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hr : 0 < rate p a) : PMF A :=
  PMF.ofFintype (fun x ↦ ENNReal.ofReal (mass p x * a x / rate p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦
      div_nonneg (mul_nonneg (mass_nonneg p x) (ha x)) hr.le), ← Finset.sum_div]
    change ENNReal.ofReal (rate p a / rate p a) = 1
    rw [div_self hr.ne', ENNReal.ofReal_one])

@[simp] theorem mass_accepted (p : PMF A) (a : A → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hr : 0 < rate p a) (x : A) :
    mass (accepted p a ha hr) x = mass p x * a x / rate p a := by
  exact ENNReal.toReal_ofReal (div_nonneg (mul_nonneg (mass_nonneg p x) (ha x)) hr.le)

theorem rate_mono (p : PMF A) (a b : A → ℝ) (hab : ∀ x, a x ≤ b x) :
    rate p a ≤ rate p b := Finset.sum_le_sum fun x _ ↦
      mul_le_mul_of_nonneg_left (hab x) (mass_nonneg p x)

/-- An unnormalized ideal rejection law may use weights exceeding one. If
clipping is confined to a target event of mass δ, at least `1-δ` of its
normalizing mass survives. This is the normalization estimate in Appendix B. -/
theorem rate_ge_of_exception (p d : PMF A) (a b : A → ℝ) (Z : ℝ)
    (ha : ∀ x, 0 ≤ a x)
    (hideal : ∀ x, mass p x * b x = Z * mass d x) (S : Finset A)
    (heq : ∀ x, x ∉ S → a x = b x) :
    Z * (1 - ∑ x ∈ S, mass d x) ≤ rate p a := by
  classical
  have hpoint (x : A) :
      (if x ∈ S then 0 else Z * mass d x) ≤ mass p x * a x := by
    by_cases hx : x ∈ S
    · simp only [hx, ite_true]
      exact mul_nonneg (mass_nonneg p x) (ha x)
    · simp only [hx, ite_false, heq x hx, hideal x, le_refl]
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) ↦ hpoint x)
  have he : (∑ x, if x ∈ S then (0 : ℝ) else Z * mass d x) =
      Z * (1 - ∑ x ∈ S, mass d x) := by
    have hp (x : A) : (if x ∈ S then (0 : ℝ) else Z * mass d x) =
        Z * mass d x - (if x ∈ S then Z * mass d x else 0) := by
      split_ifs <;> ring
    simp_rw [hp, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, sum_mass, mul_one]
    simp only [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun x ↦ x ∈ S) = S := by ext; simp
    rw [hf, ← Finset.mul_sum]
    ring
  rwa [he] at hs

/-- Pointwise distortion after clipping: the normalized accepted law is
dominated by the ideal target law by at most `1/(1-δ)`. -/
theorem accepted_le_target (p d : PMF A) (a b : A → ℝ) (Z δ : ℝ)
    (hZ : 0 < Z) (hδ : δ < 1) (ha : ∀ x, 0 ≤ a x)
    (hab : ∀ x, a x ≤ b x)
    (hideal : ∀ x, mass p x * b x = Z * mass d x)
    (hlower : Z * (1 - δ) ≤ rate p a) (x : A) :
    mass (accepted p a ha (lt_of_lt_of_le (mul_pos hZ (sub_pos.mpr hδ)) hlower)) x ≤
      mass d x / (1 - δ) := by
  rw [mass_accepted]
  have hr : 0 < rate p a := lt_of_lt_of_le (mul_pos hZ (sub_pos.mpr hδ)) hlower
  apply (div_le_div_iff₀ hr (sub_pos.mpr hδ)).mpr
  have hnum : mass p x * a x ≤ Z * mass d x :=
    (mul_le_mul_of_nonneg_left (hab x) (mass_nonneg p x)).trans_eq (hideal x)
  calc
    mass p x * a x * (1 - δ) ≤ Z * mass d x * (1 - δ) :=
      mul_le_mul_of_nonneg_right hnum (sub_pos.mpr hδ).le
    _ = mass d x * (Z * (1 - δ)) := by ring
    _ ≤ mass d x * rate p a := mul_le_mul_of_nonneg_left hlower (mass_nonneg d x)

/-- Pointwise domination of normalized laws controls total variation. -/
theorem variation_le_of_domination (p d : PMF A) (δ : ℝ) (hδ : 0 ≤ δ)
    (hdom : ∀ x, (1 - δ) * mass p x ≤ mass d x) : variation p d ≤ δ := by
  have hpoint (x : A) : |mass p x - mass d x| ≤
      mass d x - mass p x + 2 * δ * mass p x := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg hδ (mass_nonneg p x)]
    · nlinarith [hdom x]
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) ↦ hpoint x)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_mass] at hs
  unfold variation
  linarith

theorem accepted_close (p d : PMF A) (a b : A → ℝ) (Z δ : ℝ)
    (hZ : 0 < Z) (hδ₀ : 0 ≤ δ) (hδ : δ < 1) (ha : ∀ x, 0 ≤ a x)
    (hab : ∀ x, a x ≤ b x)
    (hideal : ∀ x, mass p x * b x = Z * mass d x)
    (hlower : Z * (1 - δ) ≤ rate p a) :
    variation (accepted p a ha (lt_of_lt_of_le (mul_pos hZ (sub_pos.mpr hδ)) hlower)) d ≤ δ := by
  apply variation_le_of_domination _ _ δ hδ₀
  intro x
  have h := accepted_le_target p d a b Z δ hZ hδ ha hab hideal hlower x
  have hh := (le_div_iff₀ (sub_pos.mpr hδ)).mp h
  nlinarith

end BBCR.Rejection
