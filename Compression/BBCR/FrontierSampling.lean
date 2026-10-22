module

public import BBCR.FrontierLikelihood
public import BBCR.SmoothingScale

/-! A uniform polynomial bad-mass bound and quantitative accepted-law
estimates. These are sampling laws; communication is handled separately. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.ProtocolFrontier

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def samplingError (C : ℕ) (α : ℝ) : ℝ := 2 * (α / ((C : ℝ) + 1)) ^ 4

theorem samplingError_mem (C : ℕ) (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1 / 2) :
    samplingError C α ∈ Set.Icc 0 (1 / 8) := by
  have hC : (1 : ℝ) ≤ (C : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) C]
  have hr₀ : 0 ≤ α / ((C : ℝ) + 1) := by positivity
  have hr₁ : α / ((C : ℝ) + 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < (C : ℝ) + 1)).mpr
    linarith
  have hh : (α / ((C : ℝ) + 1)) ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := by gcongr
  constructor
  · exact mul_nonneg (by norm_num) (pow_nonneg hr₀ _)
  · dsimp only [samplingError]
    norm_num at hh
    linarith

/-- Reciprocal-logarithmic smoothness makes the clipping error polynomially
small, with a constant clipping level independent of the protocol. -/
theorem badMass_polynomial (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (C : ℕ) (α β : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1 / 2) (hβ₀ : 0 < β)
    (hβ : β ≤ 1 / (4608 * SmoothingCoupling.smoothingScale C α)) (hsmooth : Smooth p β)
    (r : R) (v : List Bool) (xy : X × Y) (hr : Reached p μ r xy v) :
    TwoPartyRejection.badMass (observerFinite p μ r v xy β) (aliceFinite p μ r v xy β)
      (bobFinite p μ r v xy β) (targetFinite p μ r v xy β) (Real.exp 1) ≤ samplingError C α := by
  let L := SmoothingCoupling.smoothingScale C α
  have hL : 1 / 2 ≤ L := SmoothingCoupling.smoothingScale_half_le C α hα₀ hα₁
  have hL₀ : 0 < L := by linarith
  have hprod : β * (4608 * L) ≤ 1 := (le_div_iff₀ (by positivity)).mp hβ
  have hβ₁ : β ≤ 1 / 18 := by
    nlinarith [mul_nonneg hβ₀.le (show 0 ≤ L - 1 / 2 by linarith)]
  apply (badMass_exp_one p μ β hβ₀ hβ₁ hsmooth r v xy hr).trans
  have he : -(1 / (1152 * β)) ≤ -4 * L := by
    have hh : 4 * L ≤ 1 / (1152 * β) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    linarith
  have hexp := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num : (0 : ℝ) ≤ 2)
  have heq : Real.exp (-4 * L) = (α / ((C : ℝ) + 1)) ^ 4 := by
    rw [show -4 * L = (4 : ℕ) * (-Real.log (((C : ℝ) + 1) / α)) by
      dsimp only [L, SmoothingCoupling.smoothingScale]
      push_cast
      ring]
    rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by positivity)]
    congr 1
    simp only [inv_div]
  exact hexp.trans_eq (by rw [heq]; rfl)

/-- The accepted frontier law now comes with proved positive acceptance,
distortion, and pointwise domination, with no bad-mass assumption. -/
theorem accepted_frontier_bounds (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (C : ℕ) (α β : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1 / 2) (hβ₀ : 0 < β)
    (hβ : β ≤ 1 / (4608 * SmoothingCoupling.smoothingScale C α)) (hsmooth : Smooth p β)
    (r : R) (v : List Bool) (xy : X × Y) (hr : Reached p μ r xy v) :
    let O := observerFinite p μ r v xy β
    let P := aliceFinite p μ r v xy β
    let Q := bobFinite p μ r v xy β
    let D := targetFinite p μ r v xy β
    let a := TwoPartyRejection.acceptWeight O P Q (Real.exp 1)
    ∃ hrate : 0 < Rejection.rate O a,
      (7 / 8) / (Real.exp 1) ^ 2 ≤ Rejection.rate O a ∧
      variation (Rejection.accepted O a (TwoPartyRejection.accept_nonneg O P Q _ (Real.exp_pos _)) hrate) D
        ≤ samplingError C α ∧
      ∀ w, mass (Rejection.accepted O a (TwoPartyRejection.accept_nonneg O P Q _ (Real.exp_pos _)) hrate) w
        ≤ mass D w / (1 - samplingError C α) := by
  dsimp only
  have hL := SmoothingCoupling.smoothingScale_half_le C α hα₀ hα₁
  have hprod := (le_div_iff₀ (by positivity : 0 < 4608 * SmoothingCoupling.smoothingScale C α)).mp hβ
  have hsmall : β < 1 / 2 := by
    nlinarith [mul_nonneg hβ₀.le (show 0 ≤ SmoothingCoupling.smoothingScale C α - 1 / 2 by linarith)]
  have hbad := badMass_polynomial p μ C α β hα₀ hα₁ hβ₀ hβ hsmooth r v xy hr
  have hδ := samplingError_mem C α hα₀.le hα₁
  have hbad₁ : TwoPartyRejection.badMass (observerFinite p μ r v xy β) (aliceFinite p μ r v xy β)
      (bobFinite p μ r v xy β) (targetFinite p μ r v xy β) (Real.exp 1) < 1 := by linarith [hδ.2]
  have hC := observer_positive p μ r v xy β β hsmooth hsmall hr.2
  have hf := finite_factorization p μ r v xy β
  have hrate := TwoPartyRejection.rate_pos _ _ _ _ (Real.exp 1) (Real.exp_pos 1) hC hf hbad₁
  refine ⟨hrate, ?_, (TwoPartyRejection.accepted_close _ _ _ _ (Real.exp 1) (Real.exp_pos 1) hC hf hbad₁).trans hbad, ?_⟩
  · have hh := TwoPartyRejection.rate_lower _ _ _ _ (Real.exp 1) (Real.exp_pos 1) hC hf
    have hden : 0 < (Real.exp (1 : ℝ)) ^ 2 := by positivity
    apply (div_le_iff₀ hden).mpr
    have hmul := mul_le_mul_of_nonneg_right hh hden.le
    field_simp at hmul
    nlinarith [hδ.2]
  · intro w
    apply (TwoPartyRejection.accepted_mass_le _ _ _ _ (Real.exp 1) (Real.exp_pos 1) hC hf hbad₁ w).trans
    apply div_le_div_of_nonneg_left (mass_nonneg _ _) (by linarith [hδ.2]) (by linarith)

end BBCR.ProtocolFrontier
