module

public import Disjointness.BinaryInformation

/-! Finite KL divergence in nats, with explicit support conditions. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger

namespace BBCR

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The support hypothesis required by the real-valued finite KL formula.
Without it, `Real.log 0 = 0` would incorrectly erase infinite divergences. -/
def Supported (p q : PMF A) : Prop := ∀ a, mass q a = 0 → mass p a = 0

noncomputable def divergence (p q : PMF A) : ℝ :=
  ∑ a, mass p a * Real.log (mass p a / mass q a)

@[simp] theorem divergence_self (p : PMF A) : divergence p p = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  by_cases h : mass p a = 0
  · simp [h]
  · simp [h]

omit [Fintype A] in
theorem divergence_term (p q : PMF A) (h : Supported p q) (a : A) :
    mass p a * Real.log (mass p a / mass q a) =
      -negMulLog (mass p a) - mass p a * Real.log (mass q a) := by
  by_cases hp : mass p a = 0
  · simp [hp, negMulLog]
  · have hq : mass q a ≠ 0 := fun hq ↦ hp (h a hq)
    rw [Real.log_div hp hq, negMulLog_eq_neg]
    ring

theorem divergence_nonneg (p q : PMF A) (h : Supported p q) :
    0 ≤ divergence p q := by
  have hpoint (a : A) : mass p a - mass q a ≤
      mass p a * Real.log (mass p a / mass q a) := by
    by_cases hp : mass p a = 0
    · simp only [hp, zero_div, zero_mul, zero_sub]
      exact neg_nonpos.mpr (mass_nonneg q a)
    · have hp' : 0 < mass p a := lt_of_le_of_ne (mass_nonneg p a) (Ne.symm hp)
      have hq : mass q a ≠ 0 := fun hq ↦ hp (h a hq)
      have hq' : 0 < mass q a := lt_of_le_of_ne (mass_nonneg q a) (Ne.symm hq)
      have hl := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hq' hp')) (mass_nonneg p a)
      rw [Real.log_div hq hp] at hl
      rw [Real.log_div hp hq]
      have he : mass p a * (mass q a / mass p a - 1) = mass q a - mass p a := by
        field_simp
      rw [he] at hl
      nlinarith
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦ hpoint a)
  simpa only [Finset.sum_sub_distrib, sum_mass, sub_self, divergence] using hs

omit [Fintype B] in
theorem supported_mixture (w : PMF A) (K : A → PMF B) (a : A)
    (ha : mass w a ≠ 0) : Supported (K a) (w.bind K) := by
  intro b hb
  have hs := Disjointness.Channel.mass_bind w K b
  rw [hb] at hs
  have hz : mass w a * mass (K a) b = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun x (_ : x ∈ Finset.univ) ↦ mul_nonneg (mass_nonneg w x) (mass_nonneg (K x) b))).mp
      hs.symm a (Finset.mem_univ a)
  exact (mul_eq_zero.mp hz).resolve_left ha

/-- Uniform likelihood-ratio control bounds finite KL. -/
theorem divergence_le_log_ratio (p q : PMF A) (l u : ℝ) (hl : 0 < l)
    (hp : ∀ a, mass p a ≤ u) (hq : ∀ a, l ≤ mass q a) :
    divergence p q ≤ Real.log (u / l) := by
  have hpoint (a : A) : mass p a * Real.log (mass p a / mass q a) ≤
      mass p a * Real.log (u / l) := by
    by_cases ha : mass p a = 0
    · simp [ha]
    · have hpa : 0 < mass p a := lt_of_le_of_ne (mass_nonneg p a) (Ne.symm ha)
      have hqa : 0 < mass q a := hl.trans_le (hq a)
      apply mul_le_mul_of_nonneg_left _ (mass_nonneg p a)
      apply Real.log_le_log (div_pos hpa hqa)
      exact (div_le_div_iff₀ hqa hl).mpr
        ((mul_le_mul_of_nonneg_right (hp a) hl.le).trans
          (mul_le_mul_of_nonneg_left (hq a) (hpa.le.trans (hp a))))
  calc
    divergence p q ≤ ∑ a, mass p a * Real.log (u / l) :=
      Finset.sum_le_sum fun a _ ↦ hpoint a
    _ = Real.log (u / l) := by rw [← Finset.sum_mul, sum_mass, one_mul]

/-- Explicit version of BBCR Proposition 8.6. -/
theorem smooth_divergence_le (p q : PMF A) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1 / 4)
    (hp : ∀ a, mass p a ≤ 1 / 2 + β) (hq : ∀ a, 1 / 2 - β ≤ mass q a) :
    divergence p q ≤ 8 * β := by
  have hl : 0 < 1 / 2 - β := by linarith
  have hu : 0 < 1 / 2 + β := by linarith
  apply (divergence_le_log_ratio p q (1 / 2 - β) (1 / 2 + β) hl hp hq).trans
  apply (Real.log_le_sub_one_of_pos (div_pos hu hl)).trans
  rw [sub_le_iff_le_add, div_le_iff₀ hl]
  nlinarith

section Entropy

variable [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [MeasurableSpace B] [DiscreteMeasurableSpace B]

/-- General finite-channel version of the information/divergence identity
used in BBCR Proposition 4.9 and Lemma 8.2. Null input fibers have weight zero. -/
theorem information_eq_average_divergence (w : PMF A) (K : A → PMF B) :
    Disjointness.Channel.information w K =
      ∑ a, mass w a * divergence (K a) (w.bind K) := by
  rw [Disjointness.Channel.information_eq_entropy]
  simp_rw [Disjointness.Channel.entropy_pmf]
  have hterm (a : A) (b : B) :
      mass w a * (mass (K a) b * Real.log (mass (K a) b / mass (w.bind K) b)) =
        mass w a * (-negMulLog (mass (K a) b) -
          mass (K a) b * Real.log (mass (w.bind K) b)) := by
    by_cases ha : mass w a = 0
    · simp [ha]
    · rw [divergence_term _ _ (supported_mixture w K a ha)]
  simp only [divergence, Finset.mul_sum]
  simp_rw [hterm, mul_sub, mul_neg, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun a b ↦
    mass w a * (mass (K a) b * Real.log (mass (w.bind K) b)))]
  have hcross (b : B) :
      (∑ a, mass w a * (mass (K a) b * Real.log (mass (w.bind K) b))) =
        -negMulLog (mass (w.bind K) b) := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, ← Disjointness.Channel.mass_bind, negMulLog_eq_neg]
    ring
  simp_rw [hcross, Finset.sum_neg_distrib]
  ring

/-- Zero information means every positive-mass input has the same output law.
This is the exact zero-information case required by a compression bound with
no additive communication overhead. -/
theorem channel_constant_of_information_zero (w : PMF A) (K : A → PMF B)
    (hinfo : Disjointness.Channel.information w K = 0) (a : A) (ha : mass w a ≠ 0) :
    K a = w.bind K := by
  let : FiniteRange (Prod.fst : A × B → A) := ⟨Set.finite_range _⟩
  let : FiniteRange (Prod.snd : A × B → B) := ⟨Set.finite_range _⟩
  have hi : IndepFun (Prod.fst : A × B → A) Prod.snd (joint w K).toMeasure := by
    apply (mutualInfo_eq_zero measurable_fst measurable_snd).mp
    exact hinfo
  have hm := hi.map_prod_eq_prod_map_map measurable_fst.aemeasurable measurable_snd.aemeasurable
  change (joint w K).toMeasure.map id =
    ((joint w K).toMeasure.map Prod.fst).prod ((joint w K).toMeasure.map Prod.snd) at hm
  rw [Measure.map_id, PMF.toMeasure_map _ _ measurable_fst, joint_map_fst,
    PMF.toMeasure_map _ _ measurable_snd, Disjointness.Channel.joint_map_snd] at hm
  have he : joint w K = joint w (fun _ ↦ w.bind K) := by
    apply PMF.toMeasure_injective
    rw [hm, joint_const_toMeasure]
  apply PMF.ext
  intro b
  have hv := congrArg (fun p : PMF (A × B) ↦ mass p (a,b)) he
  simp only [mass, joint_apply, ENNReal.toReal_mul] at hv
  have hh : mass (K a) b = mass (w.bind K) b := (mul_left_cancel₀ ha hv)
  exact (ENNReal.toReal_eq_toReal_iff' ((K a).apply_ne_top b) ((w.bind K).apply_ne_top b)).mp hh

end Entropy
end BBCR
