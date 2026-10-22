module

public import BBCR.KernelCoupling
public import BBCR.LogLikelihood
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! One finite public random table couples a finite family of Bernoulli laws
by common thresholds. Public seeds are finite, even though Lebesgue measure
is used to define and verify their probability masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR

variable {A : Type} [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]

theorem probability_eq_measureReal (p : PMF A) (E : A → Prop) :
    probability p E = (p.toMeasure {a | E a}).toReal := by
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases h : E a <;> simp [Set.indicator,h,mass]
  · intro a _
    by_cases h : E a <;> simp [Set.indicator,h,PMF.apply_ne_top]

end BBCR

namespace BBCR.ThresholdCoupling

variable {I : Type} [Fintype I]

noncomputable def threshold (q : I → ℝ) (u : ℝ) : I → Bool := fun i ↦ if u < q i then true else false

omit [Fintype I] in
theorem threshold_measurable (q : I → ℝ) : Measurable (threshold q) := by
  apply Measurable.of_eval
  intro i
  have hh : Measurable (fun u : ℝ ↦ if u < q i then true else false) :=
    Measurable.ite measurableSet_Iio measurable_const measurable_const
  exact hh

noncomputable def unitMeasure : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance : IsProbabilityMeasure unitMeasure := by
  constructor
  simp [unitMeasure,Real.volume_Ico]

noncomputable def law (q : I → ℝ) : PMF (I → Bool) := (unitMeasure.map (threshold q)).toPMF

theorem law_measure (q : I → ℝ) : (law q).toMeasure = unitMeasure.map (threshold q) := by
  unfold law
  exact Measure.toPMF_toMeasure _

theorem probability_cut (q : I → ℝ) (E : (I → Bool) → Prop) (c : ℝ)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (hE : ∀ u, E (threshold q u) ↔ u < c) :
    probability (law q) E = c := by
  rw [probability_eq_measureReal, law_measure, Measure.map_apply (threshold_measurable q) (.of_discrete),
    unitMeasure, Measure.restrict_apply ((threshold_measurable q) (.of_discrete))]
  have he : threshold q ⁻¹' {t | E t} ∩ Set.Ico 0 1 = Set.Ico 0 c := by
    ext u
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_Ico,hE]
    constructor
    · rintro ⟨hu,hv⟩
      exact ⟨hv.1,hu⟩
    · rintro ⟨hu,hv⟩
      exact ⟨hv,hu,hv.trans_le hc₁⟩
  rw [he,Real.volume_Ico]
  simpa only [sub_zero] using ENNReal.toReal_ofReal hc₀

theorem marginal (q : I → ℝ) (hq₀ : ∀ i, 0 ≤ q i) (hq₁ : ∀ i, q i ≤ 1) (i : I) :
    probability (law q) (fun t ↦ t i = true) = q i := by
  apply probability_cut q _ (q i) (hq₀ i) (hq₁ i)
  intro u
  simp [threshold]

theorem both (q : I → ℝ) (hq₀ : ∀ i, 0 ≤ q i) (hq₁ : ∀ i, q i ≤ 1) (i j : I) :
    probability (law q) (fun t ↦ t i = true ∧ t j = true) = min (q i) (q j) := by
  apply probability_cut q _ (min (q i) (q j)) (le_min (hq₀ i) (hq₀ j)) ((min_le_left _ _).trans (hq₁ i))
  intro u
  simp [threshold,lt_min_iff]

theorem disagreement (q : I → ℝ) (hq₀ : ∀ i, 0 ≤ q i) (hq₁ : ∀ i, q i ≤ 1) (i j : I) :
    probability (law q) (fun t ↦ t i ≠ t j) = |q i - q j| := by
  have ha := marginal q hq₀ hq₁ i
  have hb := marginal q hq₀ hq₁ j
  have hc := both q hq₀ hq₁ i j
  have he : probability (law q) (fun t ↦ t i ≠ t j) =
      probability (law q) (fun t ↦ t i = true) + probability (law q) (fun t ↦ t j = true) -
        2 * probability (law q) (fun t ↦ t i = true ∧ t j = true) := by
    unfold probability
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    cases hi : t i <;> cases hj : t j <;> simp [hi,hj]
    ring
  rw [he,ha,hb,hc]
  by_cases hh : q i ≤ q j
  · rw [min_eq_left hh, abs_of_nonpos (sub_nonpos.mpr hh)]
    ring
  · rw [min_eq_right (le_of_not_ge hh), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hh))]
    ring

noncomputable def couple (P : I → PMF Bool) : PMF (I → Bool) := law (fun i ↦ mass (P i) true)

theorem mass_true_le_one (P : PMF Bool) : mass P true ≤ 1 := by
  have hh := sum_mass P
  simp only [Fintype.sum_bool] at hh
  linarith [mass_nonneg P false]

theorem couple_marginal (P : I → PMF Bool) (i : I) : (couple P).map (fun t ↦ t i) = P i := by
  have ht : mass ((couple P).map (fun t ↦ t i)) true = mass (P i) true := by
    rw [mass_map_sum]
    exact marginal _ (fun j ↦ mass_nonneg _ _) (fun j ↦ mass_true_le_one _) i
  have hs := sum_mass ((couple P).map (fun t ↦ t i))
  have hp := sum_mass (P i)
  simp only [Fintype.sum_bool] at hs hp
  apply PMF.ext
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change mass _ b = mass _ b
  cases b
  · linarith
  · exact ht

theorem couple_disagreement (P : I → PMF Bool) (i j : I) :
    probability (couple P) (fun t ↦ t i ≠ t j) = variation (P i) (P j) := by
  rw [variation_bool]
  exact disagreement _ (fun k ↦ mass_nonneg _ _) (fun k ↦ mass_true_le_one _) i j

end BBCR.ThresholdCoupling
