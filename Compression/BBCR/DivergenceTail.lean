module

public import BBCR.PublicInformation
public import BBCR.FiniteCoupling

/-! The basic divergence tail bound for an actual protocol under an arbitrary
correlated prior. This is the Markov consequence of Lemma 8.2, before the
stronger good-run comparison needed for smoothing. -/

@[expose] public section

open Disjointness Disjointness.Hellinger

namespace BBCR

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

/-- A protocol's accumulated divergence exceeds any positive threshold with
probability at most external information divided by that threshold. -/
theorem divergence_tail_le (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (t : ℝ) (ht : 0 < t) :
    (∑ r, mass p.publicLaw r * probability (Prefix.Prior.execution p μ)
      (fun ω ↦ t ≤ Prefix.Prior.pathDivergence p μ r p.cost ω)) ≤ externalInformation p μ / t := by
  calc
    _ ≤ ∑ r, mass p.publicLaw r *
        ((∑ ω, mass (Prefix.Prior.execution p μ) ω * Prefix.Prior.pathDivergence p μ r p.cost ω) / t) :=
      Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_left
        (probability_le_expect_div _ _ t ht (Prefix.Prior.pathDivergence_nonneg p μ r p.cost))
        (mass_nonneg p.publicLaw r)
    _ = _ := by
      simp only [← mul_div_assoc, ← Finset.sum_div]
      rw [expected_divergence_eq_externalInformation]

end BBCR
