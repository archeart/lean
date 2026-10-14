module

public import Disjointness.EmbeddingInformation

/-! The complete finite-model BJKS information and communication lower bounds. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Disjointness.Protocol

open FiniteLaw Hellinger Channel

variable {n : ℕ} {R SA SB : Type*} [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

theorem coordinate_average_lower_bound (p : Protocol (Bits n) (Bits n) R SA SB)
    (hc : p.Correct disj (1 / 3)) (i : Fin n) :
    (1 : ℝ) / 144 ≤ ∑ d, mass (Switch.switches n) d * p.coordinateInformation i d := by
  rw [← Switch.average_resample i (p.coordinateInformation i)]
  simp_rw [← p.embed_informationCost]
  calc
    (1 : ℝ) / 144 = ∑ d, mass (Switch.switches n) d * (1 / 144) := by
      rw [← Finset.sum_mul, sum_mass, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun d _ ↦ mul_le_mul_of_nonneg_left
      ((p.embed i d).and_information_lower_bound (p.embed_correct hc i d)) (mass_nonneg _ _))

/-- BJKS's linear conditional-information lower bound, in nats. -/
theorem bjks_information_lower_bound (p : Protocol (Bits n) (Bits n) R SA SB)
    (hc : p.Correct disj (1 / 3)) : (n : ℝ) / 144 ≤ p.bjksInformationCost := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ p.coordinate_average_lower_bound hc i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  calc
    (n : ℝ) / 144 ≤ ∑ i, ∑ d, mass (Switch.switches n) d * p.coordinateInformation i d := by
      simpa only [div_eq_mul_inv, one_mul] using h
    _ ≤ p.bjksInformationCost := p.bjksInformationCost_ge_sum_coordinates

end Disjointness.Protocol

namespace Disjointness

/-- Explicit positive linear constant, with information measured in nats. -/
noncomputable def lowerBoundConstant : ℝ := 1 / (144 * Real.log 2)

theorem lowerBoundConstant_pos : 0 < lowerBoundConstant := by
  unfold lowerBoundConstant
  positivity

/-- Every finite-seed interactive DISJ protocol with worst-case error at most
`1/3` has tree-depth communication cost at least `n / (144 log 2)` bits.
The theorem includes dimension zero and imposes no bound on seed cardinalities. -/
theorem disjointness_lower_bound {n : ℕ} {R SA SB : Type*}
    [Fintype R] [Fintype SA] [Fintype SB]
    (p : Protocol (Bits n) (Bits n) R SA SB) (hc : p.Correct disj (1 / 3)) :
    lowerBoundConstant * (n : ℝ) ≤ (p.cost : ℝ) := by
  let : MeasurableSpace R := ⊤
  let : DiscreteMeasurableSpace R := ⟨fun _ ↦ trivial⟩
  let : MeasurableSpace SA := ⊤
  let : DiscreteMeasurableSpace SA := ⟨fun _ ↦ trivial⟩
  let : MeasurableSpace SB := ⊤
  let : DiscreteMeasurableSpace SB := ⟨fun _ ↦ trivial⟩
  have hl := p.bjks_information_lower_bound hc
  have hu := p.bjksInformationCost_le
  unfold lowerBoundConstant
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (show 0 < 144 * Real.log 2 by positivity)).mpr
  nlinarith

/-- The original finite-model target proposition, now proved. -/
theorem finiteLowerBoundClaim : FiniteLowerBoundClaim := by
  refine ⟨lowerBoundConstant, lowerBoundConstant_pos, 0, ?_⟩
  intro n _ R SA SB _ _ _ p hc
  exact disjointness_lower_bound p hc

end Disjointness
