module

public import BBCR.LikelihoodSimulator

/-! Averaged communication and error bounds for the concrete simulator. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.FiniteAzuma

variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype B] in
theorem expect_mul (p : PMF A) (c : ℝ) (f : A → ℝ) : expect p (fun a ↦ c * f a) = c * expect p f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [Fintype B] in
theorem expect_div (p : PMF A) (f : A → ℝ) (c : ℝ) : expect p (fun a ↦ f a / c) = expect p f / c := by
  simp only [expect, div_eq_mul_inv, mul_assoc, Finset.sum_mul]

theorem expect_comm (p : PMF A) (q : PMF B) (f : A → B → ℝ) :
    expect p (fun a ↦ expect q (f a)) = expect q (fun b ↦ expect p (fun a ↦ f a b)) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end BBCR.FiniteAzuma

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier FiniteAzuma

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

noncomputable def communicationCoefficient (C : ℕ) : ℝ := 8 * Real.exp 4 * FrontierLocation.width C / acceptanceRate

theorem communicationCoefficient_nonneg (C : ℕ) : 0 ≤ communicationCoefficient C :=
  div_nonneg (by unfold FrontierLocation.width; positivity) acceptanceRate_pos.le

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem indexCoefficient_le (p : Disjointness.Protocol X Y R SA SB) (r : R) :
    indexCoefficient p r ≤ communicationCoefficient p.cost := by
  apply div_le_div_of_nonneg_right _ acceptanceRate_pos.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Nat.clog_mono_right 2 (Nat.add_le_add_right (p.depth_le_cost r) 1)

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

theorem simulator_fidelity_bound (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε)
    (n Q : ℕ) (hn : 0 < n) (hQ : 4 * n < Q) :
    (simulator p μ ε n Q).fidelityError μ ≤
      communicationCoefficient p.cost * externalInformation p μ / ((Q : ℝ) - 4 * n) +
      8 * externalInformation p μ / (acceptanceRate * n) + Real.exp (-(acceptanceRate ^ 2 * n / 8)) := by
  have ht : 0 ≤ (Q : ℝ) - 4 * n := by
    have hh : (4 : ℝ) * n < Q := by exact_mod_cast hQ
    linarith
  have hpoint (xy : X × Y) : variation
      (((simulator p μ ε n Q).protocol.finiteViewLaw xy.1 xy.2).map ((simulator p μ ε n Q).aliceDecode xy.1))
      (p.finiteViewLaw xy.1 xy.2) ≤
      expect p.publicLaw (fun r ↦ communicationCoefficient p.cost * residual p μ r xy [] / ((Q : ℝ) - 4 * n) +
        8 * residual p μ r xy [] / (acceptanceRate * n) + Real.exp (-(acceptanceRate ^ 2 * n / 8))) := by
    apply (simulator_pointwise_fidelity p μ ε hε₀ hε hsmooth n Q hn hQ xy).trans
    apply Finset.sum_le_sum
    intro r _
    apply mul_le_mul_of_nonneg_left _ (mass_nonneg _ _)
    dsimp only
    exact add_le_add (add_le_add (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (indexCoefficient_le p r)
        (residual_nonneg p μ ε hε₀ hε hsmooth r xy [] (reached_nil p μ r xy))) ht) le_rfl) le_rfl
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun xy _ ↦ mul_le_mul_of_nonneg_left (hpoint xy) (mass_nonneg μ xy))
  change (simulator p μ ε n Q).fidelityError μ ≤
    expect μ (fun xy ↦ expect p.publicLaw (fun r ↦ _)) at hh
  rw [expect_comm] at hh
  simp_rw [expect_add, expect_div, expect_mul, expect_const] at hh
  have havg := average_residual_root p μ
  change expect p.publicLaw (fun r ↦ expect μ (fun xy ↦ residual p μ r xy [])) = externalInformation p μ at havg
  rw [havg] at hh
  exact hh

end BBCR.LikelihoodFrontier
