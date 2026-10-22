module

public import BBCR.ZeroInformation

/-! The quantitative low-information case: public sampling of the transcript
marginal uses zero communication and has squared fidelity error at most the
original external information. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.Hellinger

namespace BBCR

variable {A B : Type*} [Fintype A] [Fintype B]

theorem variation_sq_le_divergence (p q : PMF A) (hs : Supported p q) :
    variation p q ^ 2 ≤ divergence p q := by
  have hh := Finset.sum_le_sum (s := Finset.univ) fun a _ ↦
    sqrt_sub_sq_le_log (mass_nonneg p a) (mass_nonneg q a) (hs a)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_mass,
    sub_add_cancel] at hh
  have he : 2 * sqDist p q ≤ divergence p q := by
    unfold sqDist divergence
    linarith
  exact (variation_sq_le p q).trans he

theorem average_variation_sq_le (w : PMF A) (K : A → PMF B) :
    (∑ a, mass w a * variation (K a) (w.bind K)) ^ 2 ≤
      ∑ a, mass w a * divergence (K a) (w.bind K) := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := fun a ↦ mass w a) (g := fun a ↦ mass w a * variation (K a) (w.bind K) ^ 2)
    (r := fun a ↦ mass w a * variation (K a) (w.bind K))
    (fun a _ ↦ mass_nonneg w a) (fun a _ ↦ mul_nonneg (mass_nonneg w a) (sq_nonneg _))
    (fun a _ ↦ le_of_eq (by ring))
  rw [sum_mass, one_mul] at hc
  refine hc.trans (Finset.sum_le_sum fun a _ ↦ ?_)
  by_cases ha : mass w a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left
      (variation_sq_le_divergence (K a) (w.bind K) (supported_mixture w K a ha)) (mass_nonneg w a)

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]

omit [Fintype SA] [Fintype SB] in
/-- A zero-communication simulator whenever information is at most the square
of the requested nonnegative error. This also handles exactly zero information. -/
theorem small_information_compression (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (α : ℝ) (hα : 0 ≤ α) (hinfo : externalInformation p μ ≤ α ^ 2) :
    ∃ s : Simulator p, s.cost = 0 ∧ s.Simulates μ α := by
  let K : X × Y → PMF p.View := fun xy ↦ p.finiteViewLaw xy.1 xy.2
  let s := publicSampler p (μ.bind K)
  refine ⟨s, publicSampler_cost _ _, ?_, ?_⟩
  · have hf : s.fidelityError μ = ∑ xy, mass μ xy * variation (K xy) (μ.bind K) := by
      unfold Simulator.fidelityError
      simp only [s, publicSampler_law]
      congr 1
      funext xy
      congr 1
      change variation (μ.bind K) (K xy) = variation (K xy) (μ.bind K)
      simp only [variation, abs_sub_comm]
    have he := average_variation_sq_le μ K
    rw [← information_eq_average_divergence] at he
    have he' : s.fidelityError μ ^ 2 ≤ externalInformation p μ := by
      rwa [hf]
    have hnonneg : 0 ≤ s.fidelityError μ := by
      unfold Simulator.fidelityError
      exact Finset.sum_nonneg fun xy _ ↦ mul_nonneg (mass_nonneg μ xy) (variation_nonneg _ _)
    nlinarith
  · simpa [s] using hα

end BBCR
