module

public import BBCR.CompressionCost
public import BBCR.SmallInformation

/-! Information-dependent compression of a smooth protocol by an actual finite
local binary protocol. The cost includes all frontier index messages. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR

open LikelihoodFrontier

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

theorem smooth_compression (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε α : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε)
    (hα : 0 < α) (hα₁ : α ≤ 1 / 2) : ∃ s : Simulator p,
      s.Simulates μ α ∧ s.cost ≤ compressionBudget compressionConstant (externalInformation p μ) p.cost α := by
  have hI := externalInformation_nonneg p μ
  have hL : 0 ≤ Real.log (((p.cost : ℝ) + 1) / α) :=
    (by
      have hh : 1 / 2 ≤ Real.log (((p.cost : ℝ) + 1) / α) := SmoothingCoupling.smoothingScale_half_le p.cost α hα hα₁
      linarith)
  by_cases hi : externalInformation p μ ≤ α ^ 2
  · obtain ⟨s,hc,hs⟩ := small_information_compression p μ α hα.le hi
    refine ⟨s,hs,?_⟩
    rw [hc, Nat.cast_zero]
    unfold compressionBudget
    exact div_nonneg (mul_nonneg (mul_nonneg compressionConstant_pos.le hI) hL) (sq_nonneg α)
  · let n := trialCount (externalInformation p μ) α
    let Q := bitCutoff p.cost (externalInformation p μ) α
    let s := simulator p μ ε n Q
    refine ⟨s,⟨?_,?_⟩,?_⟩
    · exact (simulator_fidelity_bound p μ ε hε₀ hε hsmooth n Q (trialCount_pos _ _) (bitCutoff_gt _ _ _)).trans
        (parameter_error p.cost (externalInformation p μ) α hI hα hα₁)
    · rw [simulator_agreement]
      exact hα.le
    · exact (Nat.cast_le.mpr (simulator_cost p μ ε n Q)).trans
        (bitCutoff_budget p.cost (externalInformation p μ) α hα hα₁ (le_of_not_ge hi))

end BBCR
