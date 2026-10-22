module

public import BBCR.InternalPredictions

/-! The square-root mistake estimate for the common-threshold predictions.
The averaging is over the original execution, including its private coins. -/

@[expose] public section

open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR.FiniteAzuma

variable {A : Type} [Fintype A]

theorem square_expect_le (q : PMF A) (f g : A → ℝ)
    (h : ∀ a, mass q a ≠ 0 → f a ^ 2 ≤ g a) :
    expect q f ^ 2 ≤ expect q g := by
  have hg (a : A) : 0 ≤ mass q a * g a := by
    by_cases ha : mass q a = 0
    · simp [ha]
    · exact mul_nonneg (mass_nonneg q a) ((sq_nonneg _).trans (h a ha))
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := fun a ↦ mass q a) (g := fun a ↦ mass q a * g a)
    (r := fun a ↦ mass q a * f a)
    (fun a _ ↦ mass_nonneg q a) (fun a _ ↦ hg a) (fun a _ ↦ by
      by_cases ha : mass q a = 0
      · simp [ha]
      · nlinarith [mul_le_mul_of_nonneg_left (h a ha) (sq_nonneg (mass q a))])
  simpa only [sum_mass,one_mul,expect] using hc

end BBCR.FiniteAzuma

namespace BBCR.InternalPrediction

open Prefix FiniteAzuma

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def pathDisagreement (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (n : ℕ) (ω : Prior.Sample X Y SA SB) : ℝ :=
  ∑ k ∈ Finset.range n, variation (alice p μ r ω.1.1 (Prior.history p r k ω))
    (bob p μ r ω.1.2 (Prior.history p r k ω))

theorem pathDisagreement_nonneg (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (n : ℕ) (ω : Prior.Sample X Y SA SB) :
    0 ≤ pathDisagreement p μ r n ω :=
  Finset.sum_nonneg fun _ _ ↦ variation_nonneg _ _

theorem pathDisagreement_sq_le (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (n : ℕ) (ω : Prior.Sample X Y SA SB)
    (hω : mass (Prior.execution p μ) ω ≠ 0) :
    pathDisagreement p μ r n ω ^ 2 ≤ n * Prior.internalPathDivergence p μ r n ω := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range n)
    (f := fun _ ↦ (1 : ℝ))
    (g := fun k ↦ Prior.internalNodeDivergence p μ r (Prior.history p r k ω) ω.1)
    (r := fun k ↦ variation (alice p μ r ω.1.1 (Prior.history p r k ω))
      (bob p μ r ω.1.2 (Prior.history p r k ω)))
    (fun _ _ ↦ zero_le_one)
    (fun k _ ↦ (sq_nonneg _).trans (mistake_sq_le p μ r k ω hω))
    (fun k _ ↦ by simpa using mistake_sq_le p μ r k ω hω)
  simpa only [pathDisagreement,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,
    Prior.internalPathDivergence_eq_sum] using hc

variable [Fintype R]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

noncomputable def expectedDisagreement (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) : ℝ :=
  ∑ r, mass p.publicLaw r * expect (Prior.execution p μ) (pathDisagreement p μ r p.cost)

theorem expectedDisagreement_sq_le (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) :
    expectedDisagreement p μ ^ 2 ≤ p.cost * internalInformation p μ := by
  let q := joint p.publicLaw (fun _ ↦ Prior.execution p μ)
  have he (g : R × Prior.Sample X Y SA SB → ℝ) :
      expect q g = ∑ r, mass p.publicLaw r * expect (Prior.execution p μ) (fun ω ↦ g (r,ω)) := by
    rw [show q = p.publicLaw.bind (fun r ↦ (Prior.execution p μ).map (Prod.mk r)) from joint_eq_bind _ _,expect_bind]
    simp_rw [expect_map]
    rfl
  have hc := square_expect_le q
    (fun z ↦ pathDisagreement p μ z.1 p.cost z.2)
    (fun z ↦ p.cost * Prior.internalPathDivergence p μ z.1 p.cost z.2) (fun z hz ↦ by
      have hm : mass q z = mass p.publicLaw z.1 * mass (Prior.execution p μ) z.2 := by
        rcases z with ⟨r,ω⟩
        simp only [q,mass,joint_apply,ENNReal.toReal_mul]
      exact pathDisagreement_sq_le p μ z.1 p.cost z.2 ((mul_ne_zero_iff.mp (hm.symm.trans_ne hz)).2))
  rw [he,he] at hc
  change expectedDisagreement p μ ^ 2 ≤ _ at hc
  have hd := Prior.expected_internal_path p μ
  simp only [expect_mul] at hc
  have hr : (∑ r, mass p.publicLaw r * (p.cost * expect (Prior.execution p μ)
      (Prior.internalPathDivergence p μ r p.cost))) = p.cost * internalInformation p μ := by
    rw [← hd,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  exact hc.trans_eq hr

theorem expectedDisagreement_le_sqrt (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) :
    expectedDisagreement p μ ≤ Real.sqrt ((p.cost : ℝ) * internalInformation p μ) := by
  have h := expectedDisagreement_sq_le p μ
  exact (Real.le_sqrt (Finset.sum_nonneg fun r _ ↦ mul_nonneg (mass_nonneg p.publicLaw r)
    (Finset.sum_nonneg fun ω _ ↦ mul_nonneg (mass_nonneg (Prior.execution p μ) ω)
      (pathDisagreement_nonneg p μ r p.cost ω)))
    (mul_nonneg (Nat.cast_nonneg _) (internalInformation_nonneg p μ))).mpr h

end BBCR.InternalPrediction
