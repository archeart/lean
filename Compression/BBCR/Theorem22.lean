module

public import BBCR.SmoothCompression
public import BBCR.SimulatorComposition
public import BBCR.SmoothingLogBudget

/-! BBCR Theorem 2.2 in the finite protocol model: private-randomness interactive
compression with a uniform information-dependent single-logarithm bound. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR

open LikelihoodFrontier SmoothingCoupling

set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000

noncomputable def theorem22Constant : ℝ := 400000 * compressionConstant

theorem theorem22Constant_pos : 0 < theorem22Constant := mul_pos (by norm_num) compressionConstant_pos

theorem scale_half_error_le (C : ℕ) (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) :
    smoothingScale C (α / 2) ≤ 2 * smoothingScale C α := by
  have hr : (2 : ℝ) ≤ ((C : ℝ) + 1) / α := (le_div_iff₀ hα).mpr (by
    have hh : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    linarith)
  have hl : Real.log 2 ≤ smoothingScale C α := Real.log_le_log (by norm_num) hr
  unfold smoothingScale
  rw [show ((C : ℝ) + 1) / (α / 2) = 2 * (((C : ℝ) + 1) / α) by ring,
    Real.log_mul (by norm_num) (by positivity)]
  change Real.log 2 ≤ Real.log (((C : ℝ) + 1) / α) at hl
  linarith

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

/-- Finite-model form of BBCR Theorem 2.2, with external information in nats,
full-view fidelity, local agreement, and worst-case binary communication. -/
theorem theorem_2_2 (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1 / 2) : ∃ s : Simulator p,
      s.Simulates μ α ∧ s.cost ≤ compressionBudget theorem22Constant (externalInformation p μ) p.cost α := by
  have hI := externalInformation_nonneg p μ
  have hL : 0 ≤ smoothingScale p.cost α := (by linarith [smoothingScale_half_le p.cost α hα hα₁])
  by_cases hi : externalInformation p μ ≤ α ^ 2
  · obtain ⟨s,hc,hs⟩ := small_information_compression p μ α hα.le hi
    refine ⟨s,hs,?_⟩
    rw [hc, Nat.cast_zero]
    exact div_nonneg (mul_nonneg (mul_nonneg theorem22Constant_pos.le hI) hL) (sq_nonneg α)
  · let δ := α / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδ₁ : δ ≤ 1 / 2 := by dsimp [δ]; linarith
    let k := (32 * (16 : ℝ)) ^ 2
    let β := reciprocalBias p.cost δ k
    have hk : 1 ≤ k := by norm_num [k]
    have hb := reciprocalBias_mem p.cost δ k hδ hδ₁ hk
    let s := informationSimulator p δ β hb.1.le hb.2
    have hδI : δ ^ 2 ≤ externalInformation p μ := by dsimp [δ]; nlinarith [le_of_not_ge hi]
    have hready := smoothing_ready_for_compression p μ δ 16 hδ hδ₁ (by norm_num) hδI
    change s.Simulates μ δ ∧ Smooth s.protocol (1 / (16 * smoothingScale s.cost δ)) ∧
      externalInformation s.protocol μ ≤ 2 * externalInformation p μ ∧
      (s.cost : ℝ) ≤ 544 * k ^ 3 * smoothingScale p.cost δ ^ 3 * p.cost ∧
      smoothingScale s.cost δ ≤ 1476 * 16 * smoothingScale p.cost δ at hready
    let ε := 1 / (16 * smoothingScale s.cost δ)
    have hε₀ : 0 ≤ ε := by
      have hh := smoothingScale_half_le s.cost δ hδ hδ₁
      dsimp [ε]
      positivity
    have hε : ε ≤ 1 / 8 := by
      have hh := smoothingScale_half_le s.cost δ hδ hδ₁
      dsimp only [ε]
      exact (div_le_div_iff₀ (by linarith : 0 < 16 * smoothingScale s.cost δ) (by norm_num : (0 : ℝ) < 8)).mpr (by linarith)
    let m := informationBlockSize p.cost δ β
    let η := tapeLaw p.cost m β hb.1.le hb.2
    let q := SmoothingProtocol.protocol p m η
    obtain ⟨t,ht,hcost⟩ := smooth_compression q μ ε δ hε₀ hε hready.2.1 hδ hδ₁
    let decode := SmoothingProtocol.decodeView p m η
    let u := Simulator.composePublic s t decode
    refine ⟨u,?_,?_⟩
    · have hh := Simulator.composePublic_simulates s t decode (fun _ ↦ rfl) μ δ δ hδ.le hready.1 ht
      simpa only [δ, add_halves] using hh
    · change (t.cost : ℝ) ≤ _
      apply hcost.trans
      have hlog : smoothingScale s.cost δ ≤ 47232 * smoothingScale p.cost α := by
        have hh := scale_half_error_le p.cost α hα hα₁
        dsimp only [δ] at hready
        linarith [hready.2.2.2.2]
      have hscale : 0 ≤ smoothingScale s.cost δ := by linarith [smoothingScale_half_le s.cost δ hδ hδ₁]
      have hinfo : externalInformation q μ ≤ 2 * externalInformation p μ := hready.2.2.1
      have hc : compressionConstant * externalInformation q μ * smoothingScale s.cost δ ≤
          compressionConstant * (2 * externalInformation p μ) * (47232 * smoothingScale p.cost α) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hinfo compressionConstant_pos.le) hlog hscale
          (mul_nonneg compressionConstant_pos.le (by positivity))
      change compressionConstant * externalInformation q μ * smoothingScale s.cost δ / δ ^ 2 ≤
        theorem22Constant * externalInformation p μ * smoothingScale p.cost α / α ^ 2
      have he : compressionConstant * (2 * externalInformation p μ) * (47232 * smoothingScale p.cost α) / δ ^ 2 =
          (377856 * compressionConstant) * externalInformation p μ * smoothingScale p.cost α / α ^ 2 := by
        dsimp only [δ]
        ring
      calc
        _ ≤ _ := div_le_div_of_nonneg_right hc (sq_nonneg δ)
        _ = _ := he
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by unfold theorem22Constant; nlinarith [compressionConstant_pos]) hI) hL) (sq_nonneg α)

/-- The original uniform endpoint, with one positive constant for every finite
input alphabet, seed space, protocol, prior, and allowed simulation error. -/
theorem externalCompressionClaim : ExternalCompressionClaim := by
  refine ⟨theorem22Constant,theorem22Constant_pos,?_⟩
  intro X Y R SA SB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p μ α hα hα₁
  exact theorem_2_2 p μ α hα hα₁

end BBCR
