module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Disjointness.Hellinger

/-! Finite-PMF integration with mathlib's Hoeffding lemma. The path-dependent
Azuma estimate is proved separately in `BBCR.FiniteAzuma`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Disjointness.Hellinger

namespace BBCR

variable {A : Type*} [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]

/-- BBCR Lemma A.2, including its scaled form, for finite laws. -/
theorem finite_hoeffding (p : PMF A) (f : A → ℝ) (a b t : ℝ)
    (hbounded : ∀ x, f x ∈ Set.Icc a b) (hmean : ∑ x, mass p x * f x = 0) :
    (∑ x, mass p x * Real.exp (t * f x)) ≤ Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  have hm : ∫ x, f x ∂p.toMeasure = 0 := by
    simpa only [PMF.integral_eq_sum, smul_eq_mul, mass] using hmean
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := p.toMeasure) (X := f) (show AEMeasurable f p.toMeasure from .of_discrete)
    (Filter.Eventually.of_forall hbounded) hm
  have hh := h.mgf_le t
  simp only [mgf, PMF.integral_eq_sum, smul_eq_mul, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs, div_pow, sq_abs] at hh
  convert hh using 1
  · rfl
  · congr 1
    ring

end BBCR
