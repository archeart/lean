module

public import BBCR.SmoothingInformation
public import BBCR.SmoothingSmoothness
public import BBCR.DivergenceTail

/-! Quantitative information and divergence-tail bounds for the same iid
noisy-block simulator whose fidelity, cost, and smoothness are checked. -/

@[expose] public section

open Disjointness Disjointness.Hellinger

namespace BBCR.SmoothingCoupling

open SmoothingTree SmoothingProtocol

/-- Exponentially small failure probability of the two entire correctness
tapes. This event is independent of the original protocol experiment. -/
theorem bad_noise_le (C m : ℕ) (hm : 0 < m) (β : ℝ)
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    badNoiseProbability (tapeLaw C m β hβ₀ hβ₁) ≤
      2 * ((C : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2) := by
  refine (badNoiseProbability_le _).trans ?_
  have h := mul_le_mul_of_nonneg_left (bad_tape_le C m β hβ₀ hβ₁ hm)
    (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_assoc] using h

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R]
  [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

theorem smoothing_information_le (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (hm : 0 < m) (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    externalInformation (protocol p m (tapeLaw p.cost m β hβ₀ hβ₁)) μ ≤
      externalInformation p μ +
        (2 * ((p.cost : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2)) *
          ((m * p.cost : ℕ) : ℝ) * Real.log 2 := by
  refine (externalInformation_le_original_add_bad p μ m _).trans ?_
  refine add_le_add le_rfl ?_
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  exact mul_le_mul_of_nonneg_right (bad_noise_le p.cost m hm β hβ₀ hβ₁) (Nat.cast_nonneg _)

/-- The smoothed protocol's actual accumulated divergence, bounded using the
original external information and the explicit bad-tape correction. -/
theorem smoothing_divergence_tail_le (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (hm : 0 < m) (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2)
    (t : ℝ) (ht : 0 < t) :
    let q := protocol p m (tapeLaw p.cost m β hβ₀ hβ₁)
    (∑ r, mass q.publicLaw r * probability (Prefix.Prior.execution q μ)
      (fun ω ↦ t ≤ Prefix.Prior.pathDivergence q μ r q.cost ω)) ≤
        (externalInformation p μ +
          (2 * ((p.cost : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2)) *
            ((m * p.cost : ℕ) : ℝ) * Real.log 2) / t := by
  exact (divergence_tail_le _ μ t ht).trans
    (div_le_div_of_nonneg_right (smoothing_information_le p μ m hm β hβ₀ hβ₁) ht.le)

/-- One concrete simulator simultaneously has all four smoothing guarantees.
The information correction is explicit and still needs to be budgeted when
choosing parameters for the final compression theorem. -/
theorem smoothing_with_information (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (hm : 0 < m) (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    let s := simulator p m (tapeLaw p.cost m β hβ₀ hβ₁)
    s.cost ≤ m * p.cost ∧
      s.Simulates μ (2 * ((p.cost : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2)) ∧
      Smooth s.protocol β ∧
      externalInformation s.protocol μ ≤ externalInformation p μ +
        (2 * ((p.cost : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2)) *
          ((m * p.cost : ℕ) : ℝ) * Real.log 2 := by
  obtain ⟨hβ,hc,hs⟩ := smooth_simulation p μ m hm β hβ₀ hβ₁
  exact ⟨hc,hs,hβ,smoothing_information_le p μ m hm β hβ₀ hβ₁⟩

end BBCR.SmoothingCoupling
