module

public import BBCR.Rejection
public import BBCR.InformationChain

/-! Finite conditional laws with a harmless fallback on null fibers. Weighted
identities hold on every fiber, so later information calculations need no
arbitrary assumptions about zero-probability histories. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw

namespace BBCR.FiniteCondition

open scoped Classical

variable {Ω H A : Type*} [Fintype Ω]

/-- Joint sampling without requiring a finite output alphabet. This is useful
for the countable alphabet of variable-length protocol prefixes. -/
noncomputable def jointLaw (p : PMF Ω) (K : Ω → PMF A) : PMF (Ω × A) :=
  p.bind fun ω ↦ (K ω).map (Prod.mk ω)

omit [Fintype Ω] in
theorem jointLaw_apply (p : PMF Ω) (K : Ω → PMF A) (ω : Ω) (a : A) :
    jointLaw p K (ω,a) = p ω * K ω a := by
  rw [jointLaw, PMF.bind_apply]
  have he (ω' : Ω) : ((K ω').map (Prod.mk ω')) (ω,a) =
      if ω' = ω then K ω a else 0 := by
    by_cases h : ω' = ω
    · subst ω'
      simp [PMF.map_apply]
    · simp [PMF.map_apply, h, Ne.symm h]
  simp_rw [he, mul_ite, mul_zero]
  simp

omit [Fintype Ω] in
theorem jointLaw_map_snd (p : PMF Ω) (K : Ω → PMF A) :
    (jointLaw p K).map Prod.snd = p.bind K := by
  simp only [jointLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change p.bind (fun ω ↦ (K ω).map id) = _
  simp only [PMF.map_id]

open scoped Classical in
noncomputable def indicator (f : Ω → H) (h : H) (ω : Ω) : ℝ := if f ω = h then 1 else 0

omit [Fintype Ω] in
theorem indicator_nonneg (f : Ω → H) (h : H) (ω : Ω) : 0 ≤ indicator f h ω := by
  classical
  unfold indicator
  split_ifs <;> norm_num

theorem rate_indicator (p : PMF Ω) (f : Ω → H) (h : H) :
    Rejection.rate p (indicator f h) = mass (p.map f) h := by
  classical
  rw [Disjointness.Channel.event_mass]
  simp [Rejection.rate, indicator, Finset.sum_filter, mul_ite]

theorem mass_le_map (p : PMF Ω) (f : Ω → H) (ω : Ω) :
    mass p ω ≤ mass (p.map f) (f ω) := by
  classical
  rw [Disjointness.Channel.event_mass]
  exact Finset.single_le_sum (fun x _ ↦ mass_nonneg p x) (by simp)

theorem exists_of_mass_pos (p : PMF Ω) (f : Ω → H) (h : H)
    (hp : 0 < mass (p.map f) h) : ∃ ω, f ω = h := by
  by_contra hn
  push Not at hn
  have hz : mass (p.map f) h = 0 := by
    rw [Disjointness.Channel.event_mass]
    simp [hn]
  exact hp.ne' hz

/-- Conditional law given `f=h`. The fallback on a null fiber is the original
law; its value is always multiplied by the zero probability of that fiber. -/
noncomputable def law (p : PMF Ω) (f : Ω → H) (h : H) : PMF Ω :=
  if hp : 0 < mass (p.map f) h then
    Rejection.accepted p (indicator f h) (indicator_nonneg f h)
      (by rwa [rate_indicator])
  else p

theorem mass_law_of_pos (p : PMF Ω) (f : Ω → H) (h : H)
    (hp : 0 < mass (p.map f) h) (ω : Ω) :
    mass (law p f h) ω = (if f ω = h then mass p ω else 0) / mass (p.map f) h := by
  classical
  rw [law, dite_eq_left hp, Rejection.mass_accepted, rate_indicator]
  simp [indicator, mul_ite]

theorem weighted_mass_law (p : PMF Ω) (f : Ω → H) (h : H) (ω : Ω) :
    mass (p.map f) h * mass (law p f h) ω = if f ω = h then mass p ω else 0 := by
  classical
  by_cases hp : 0 < mass (p.map f) h
  · rw [mass_law_of_pos p f h hp]
    field_simp
  · have hz : mass (p.map f) h = 0 := le_antisymm (le_of_not_gt hp) (mass_nonneg _ _)
    rw [hz, zero_mul]
    split_ifs with hf
    · have hh := mass_le_map p f ω
      rw [hf, hz] at hh
      exact (le_antisymm hh (mass_nonneg _ _)).symm
    · rfl

/-- Conditional sampling followed by deterministic observation reconstructs the
original joint history/observation law, including all null fibers. -/
theorem weighted_observe (p : PMF Ω) (f : Ω → H) (g : Ω → A) (h : H) (a : A) :
    mass (p.map f) h * mass ((law p f h).map g) a =
      ∑ ω, if f ω = h ∧ g ω = a then mass p ω else 0 := by
  classical
  rw [Disjointness.Channel.event_mass (law p f h) g a]
  simp only [Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hg : g ω = a
  · simp only [hg, ite_true, and_true]
    exact weighted_mass_law p f h ω
  · simp [hg]

theorem weighted_pair (p : PMF Ω) (f : Ω → H) (g : Ω → A) (h : H) (a : A) :
    mass (p.map f) h * mass ((law p f h).map g) a =
      mass (p.map (fun ω ↦ (g ω, f ω))) (a,h) := by
  rw [weighted_observe, Disjointness.Channel.event_mass]
  simp only [Finset.sum_filter, Prod.mk.injEq, and_comm]

local instance conditionFiniteRange (f : Ω → H) : FiniteRange f := ⟨Set.finite_range f⟩

/-- Disintegrate an arbitrary finite statistic over the actual range of a
history map. Null histories contribute zero, regardless of their fallback law. -/
theorem sum_fibers (p : PMF Ω) (f : Ω → H) (g : H → Ω → ℝ) :
    (∑ h ∈ FiniteRange.toFinset f, mass (p.map f) h *
      ∑ ω, mass (law p f h) ω * g h ω) = ∑ ω, mass p ω * g (f ω) ω := by
  simp only [Finset.mul_sum, ← mul_assoc, weighted_mass_law]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem weighted_refinement {J : Type*} (p : PMF Ω) (f : Ω → H) (F : H → J)
    (j : J) (h : H) :
    mass (p.map (F ∘ f)) j * mass ((law p (F ∘ f) j).map f) h =
      if F h = j then mass (p.map f) h else 0 := by
  rw [weighted_observe, Disjointness.Channel.event_mass]
  simp only [Finset.sum_filter]
  by_cases hF : F h = j
  · simp only [hF, ite_true]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hf : f ω = h <;> simp [hf, hF]
  · rw [ite_eq_right hF]
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hf : f ω = h <;> simp [hf, hF]

theorem refinement_of_positive {J : Type*} (p : PMF Ω) (f : Ω → H) (F : H → J)
    (j : J) (h : H) (hj : 0 < mass (p.map (F ∘ f)) j)
    (hh : 0 < mass ((law p (F ∘ f) j).map f) h) :
    F h = j ∧ 0 < mass (p.map f) h := by
  have he := weighted_refinement p f F j h
  have hp := mul_pos hj hh
  rw [he] at hp
  split_ifs at hp with hF
  · exact ⟨hF,hp⟩
  · exact (lt_irrefl 0 hp).elim

section Measure

variable [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [MeasurableSpace H] [DiscreteMeasurableSpace H]

omit [Fintype Ω] in
theorem fiber_measure (p : PMF Ω) (f : Ω → H) (h : H) :
    p.toMeasure (f ⁻¹' {h}) = (p.map f) h := by
  rw [← PMF.toMeasure_map_apply _ _ _ (show Measurable f from .of_discrete) (.singleton _)]
  exact PMF.toMeasure_apply_singleton _ _ (.singleton _)

/-- The finite PMF conditional law is the actual measure-theoretic conditional
law used by PFR entropy, on every positive-probability history. -/
theorem toMeasure_law_of_pos (p : PMF Ω) (f : Ω → H) (h : H)
    (hp : 0 < mass (p.map f) h) :
    (law p f h).toMeasure = p.toMeasure[|f ⁻¹' {h}] := by
  classical
  apply Measure.ext_of_singleton
  intro ω
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [PMF.toMeasure_apply_singleton _ _ (.singleton _),
    cond_apply (show MeasurableSet (f ⁻¹' {h}) from .of_discrete), fiber_measure]
  change mass (law p f h) ω = _
  rw [mass_law_of_pos p f h hp]
  by_cases hf : f ω = h
  · rw [Set.inter_singleton_of_mem (show ω ∈ f ⁻¹' {h} from hf),
      PMF.toMeasure_apply_singleton _ _ (.singleton _)]
    simp only [hf, ite_true, ENNReal.toReal_mul, ENNReal.toReal_inv, mass, div_eq_mul_inv]
    ring
  · rw [Set.inter_singleton_of_notMem (show ω ∉ f ⁻¹' {h} from hf), measure_empty, mul_zero]
    simp [hf]

/-- Conditioning on a finer observation erases the earlier coarse condition.
The hypotheses concern actual positive masses, including the second fiber. -/
theorem law_refinement {J : Type*} [MeasurableSpace J] [DiscreteMeasurableSpace J]
    (p : PMF Ω) (f : Ω → H) (F : H → J) (j : J) (h : H)
    (hj : 0 < mass (p.map (F ∘ f)) j)
    (hh : 0 < mass ((law p (F ∘ f) j).map f) h) :
    law (law p (F ∘ f) j) f h = law p f h := by
  obtain ⟨hF,hp⟩ := refinement_of_positive p f F j h hj hh
  apply PMF.toMeasure_injective
  rw [toMeasure_law_of_pos _ f h hh, toMeasure_law_of_pos p (F ∘ f) j hj,
    toMeasure_law_of_pos p f h hp, cond_cond_eq_cond_inter (.of_discrete) (.of_discrete)]
  congr 1
  apply Set.inter_eq_right.mpr
  intro ω hω
  change f ω = h at hω
  change F (f ω) = j
  rw [hω, hF]

end Measure
end BBCR.FiniteCondition
