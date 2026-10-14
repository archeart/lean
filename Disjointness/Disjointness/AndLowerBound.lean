module

public import Disjointness.ChannelBridge

/-! The AND information lower bound, including worst-case correctness at `(true,true)`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Disjointness.Protocol

open FiniteLaw Hellinger Channel

variable {R SA SB : Type*} [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

noncomputable def andInformationCost (p : Protocol Bool Bool R SA SB) : ℝ :=
  p.informationCost Switch.coordinateLaw

theorem andInformationCost_eq (p : Protocol Bool Bool R SA SB) :
    p.andInformationCost = (information Switch.fair (fun b ↦ p.finiteViewLaw b false) +
      information Switch.fair (fun b ↦ p.finiteViewLaw false b)) / 2 := by
  have h₁ : joint (Switch.bitLaw true) (fun _ ↦ Switch.bitLaw (!true)) =
      Switch.fair.map (fun b ↦ (b, false)) := by
    simp [Switch.bitLaw, joint_eq_bind, ← PMF.bind_pure_comp, Function.comp_def]
  have h₀ : joint (Switch.bitLaw false) (fun _ ↦ Switch.bitLaw (!false)) =
      Switch.fair.map (fun b ↦ (false, b)) := by
    simp [Switch.bitLaw, joint_eq_bind]
  rw [andInformationCost, Switch.coordinateLaw, informationCost_eq_channel]
  simp only [conditional, Fintype.sum_bool, fair_mass, h₁, h₀, information_map,
    Function.comp_def]
  ring

omit [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem and_cut_and_paste (p : Protocol Bool Bool R SA SB) :
    sqDist (p.finiteViewLaw false false) (p.finiteViewLaw true true) =
      sqDist (p.finiteViewLaw false true) (p.finiteViewLaw true false) := by
  apply cut_and_paste
  intro v
  simpa only [mass, ENNReal.toReal_mul] using congrArg ENNReal.toReal
    (p.finiteViewLaw_rectangle false true false true v)

theorem and_separation_le_information (p : Protocol Bool Bool R SA SB) :
    sqDist (p.finiteViewLaw false false) (p.finiteViewLaw true true) ≤
      8 * p.andInformationCost := by
  rw [and_cut_and_paste]
  have ht := sqDist_triangle (p.finiteViewLaw false true)
    (p.finiteViewLaw false false) (p.finiteViewLaw true false)
  rw [sqDist_comm (p.finiteViewLaw false true) (p.finiteViewLaw false false)] at ht
  have h₀ := sqDist_le_two_information_fair (fun b ↦ p.finiteViewLaw false b)
  have h₁ := sqDist_le_two_information_fair (fun b ↦ p.finiteViewLaw b false)
  rw [andInformationCost_eq]
  linarith

omit [Fintype SA] [Fintype SB]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
/-- Only the two separated corners are needed here. Both are worst-case inputs,
including `(true,true)`, which has zero probability under the analysis law. -/
theorem and_correct_separation (p : Protocol Bool Bool R SA SB)
    (hc : p.Correct Bool.and (1 / 3)) :
    (1 : ℝ) / 18 ≤ sqDist (p.finiteViewLaw false false) (p.finiteViewLaw true true) := by
  classical
  have h₀ : mass (p.outputLaw false false) true ≤ 1 / 3 := by
    simpa only [Correct, error, Bool.and_false, Bool.not_false, mass] using hc false false
  have h₁ : mass (p.outputLaw true true) false ≤ 1 / 3 := by
    simpa only [Correct, error, Bool.and_true, Bool.not_true, mass] using hc true true
  have hs := sum_mass (p.outputLaw true true)
  simp only [Fintype.sum_bool] at hs
  have he := event_difference_le (p.finiteViewLaw false false) (p.finiteViewLaw true true)
    (Finset.univ.filter (fun v ↦ p.viewOutput v = true))
  rw [← event_mass, ← event_mass, finiteViewLaw_output, finiteViewLaw_output] at he
  have hv : (1 : ℝ) / 3 ≤ variation (p.finiteViewLaw false false) (p.finiteViewLaw true true) := by
    have := neg_le_abs (mass (p.outputLaw false false) true - mass (p.outputLaw true true) true)
    linarith
  have ht := variation_sq_le (p.finiteViewLaw false false) (p.finiteViewLaw true true)
  nlinarith

/-- A finite randomized interactive AND protocol with worst-case error at most
`1/3` reveals at least `1/144` nats under the switch law. -/
theorem and_information_lower_bound (p : Protocol Bool Bool R SA SB)
    (hc : p.Correct Bool.and (1 / 3)) : (1 : ℝ) / 144 ≤ p.andInformationCost := by
  have h₁ := p.and_correct_separation hc
  have h₂ := p.and_separation_le_information
  linarith

end Disjointness.Protocol
