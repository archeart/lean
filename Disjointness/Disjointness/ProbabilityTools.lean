module

public import Disjointness.Integration

/-! Finite joint and product laws, with explicit conditional-fiber identities. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Disjointness.FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

@[simp] theorem sum_pmf (p : PMF A) : ∑ a, p a = 1 :=
  (tsum_fintype _).symm.trans p.tsum_coe

/-- Sample the first coordinate, then the second from its specified conditional law. -/
noncomputable def joint (p : PMF A) (q : A → PMF B) : PMF (A × B) :=
  PMF.ofFintype (fun z ↦ p z.1 * q z.1 z.2) (by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum]
    simp only [sum_pmf, mul_one])

@[simp] theorem joint_apply (p : PMF A) (q : A → PMF B) (a : A) (b : B) :
    joint p q (a, b) = p a * q a b := rfl

theorem joint_eq_bind (p : PMF A) (q : A → PMF B) :
    joint p q = p.bind (fun a ↦ (q a).map (Prod.mk a)) := by
  classical
  ext ⟨a, b⟩
  simp only [PMF.bind_apply, PMF.map_apply, joint_apply, Prod.mk.injEq]
  simp_rw [ite_and]
  simp

@[simp] theorem joint_map_fst (p : PMF A) (q : A → PMF B) :
    (joint p q).map Prod.fst = p := by
  rw [joint_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change p.bind (fun a ↦ (q a).map (Function.const B a)) = p
  simp [PMF.bind_pure]

variable [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [MeasurableSpace B] [DiscreteMeasurableSpace B]

omit [DiscreteMeasurableSpace B] in
theorem joint_fiber (p : PMF A) (q : A → PMF B) (a : A) :
    (joint p q).toMeasure (Prod.fst ⁻¹' {a}) = p a := by
  rw [← PMF.toMeasure_map_apply _ _ _ measurable_fst (.singleton _), joint_map_fst]
  exact PMF.toMeasure_apply_singleton _ _ (.singleton _)

/-- A positive-probability fiber has exactly its specified conditional law.
Zero-probability fibers are handled by `cond_eq_zero_of_meas_eq_zero` instead. -/
theorem joint_cond_fst (p : PMF A) (q : A → PMF B) (a : A) (ha : p a ≠ 0) :
    (joint p q).toMeasure[|Prod.fst ⁻¹' {a}] =
      (joint (PMF.pure a) (fun _ ↦ q a)).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨a', b⟩
  rw [cond_apply (measurable_fst (.singleton _)), joint_fiber]
  by_cases h : a' = a
  · subst a'
    simp only [Set.inter_singleton_of_mem (show (a, b) ∈ Prod.fst ⁻¹' {a} from rfl),
      PMF.toMeasure_apply_singleton _ _ (.singleton _), joint_apply, PMF.pure_apply, ite_true, one_mul]
    rw [← mul_assoc, ENNReal.inv_mul_cancel ha (PMF.apply_ne_top p a), one_mul]
  · have hn : (a', b) ∉ Prod.fst ⁻¹' {a} := h
    simp only [Set.inter_singleton_of_notMem hn, measure_empty, mul_zero,
      PMF.toMeasure_apply_singleton _ _ (.singleton _),
      joint_apply, PMF.pure_apply, h, ite_false, zero_mul]

theorem joint_const_toMeasure (p : PMF A) (q : PMF B) :
    (joint p (fun _ ↦ q)).toMeasure = p.toMeasure.prod q.toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp only [Set.singleton_prod_singleton,
    PMF.toMeasure_apply_singleton _ _ (.singleton _), joint_apply]

/-- Independent finite coordinates as a PMF. -/
noncomputable def pi {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i)) : PMF (∀ i, α i) := by
  classical
  exact
  PMF.ofFintype (fun x ↦ ∏ i, p i (x i)) (by
    classical
    rw [← Fintype.prod_sum]
    simp only [sum_pmf, Finset.prod_const_one])

@[simp] theorem pi_apply {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i)) (x : ∀ i, α i) : pi p x = ∏ i, p i (x i) := rfl

theorem pi_toMeasure {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, DiscreteMeasurableSpace (α i)]
    (p : ∀ i, PMF (α i)) : (pi p).toMeasure = Measure.pi (fun i ↦ (p i).toMeasure) := by
  apply Measure.ext_of_singleton
  intro x
  simp only [PMF.toMeasure_apply_singleton _ _ (.singleton _), Measure.pi_singleton, pi_apply]

theorem pi_map_eval {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, DiscreteMeasurableSpace (α i)]
    (p : ∀ i, PMF (α i)) (i : ι) : (pi p).map (Function.eval i) = p i := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_pi_apply _), pi_toMeasure]
  exact (measurePreserving_eval (fun i ↦ (p i).toMeasure) i).map_eq

end Disjointness.FiniteLaw

namespace Disjointness.FiniteLaw

/-- Conditioning and pushforward commute when the event is a preimage.
This identity also covers events of probability zero. -/
theorem map_cond_preimage {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) {f : Ω → Ω'} (hf : Measurable f) {s : Set Ω'} (hs : MeasurableSet s) :
    (μ[|f ⁻¹' s]).map f = (μ.map f)[|s] := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul, ← Measure.restrict_map hf hs, Measure.map_apply hf hs]
  exact hf.aemeasurable

/-- Relabeling a finite distribution by an equivalence preserves point masses. -/
theorem map_equiv_apply {A B : Type*} (p : PMF A) (e : A ≃ B) (b : B) :
    p.map e b = p (e.symm b) := by
  classical
  rw [PMF.map_apply]
  have h (a : A) : b = e a ↔ a = e.symm b := by
    constructor
    · intro h; rw [h, e.symm_apply_apply]
    · intro h; rw [h, e.apply_symm_apply]
  simp_rw [h]
  simp

section Pullback

variable {Ω Ω' A B : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {f : Ω → Ω'} (hf : Measurable f) (hmap : μ.map f = ν)

include hf hmap in
theorem indep_pullback {X : Ω' → A} {Y : Ω' → B}
    (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y ν) :
    IndepFun (X ∘ f) (Y ∘ f) μ := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (hX.comp hf).aemeasurable
    (hY.comp hf).aemeasurable).mpr
  have hh := h.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  rw [← hmap] at hh
  simpa only [Measure.map_map hX hf, Measure.map_map hY hf,
    Measure.map_map (hX.prodMk hY) hf, Function.comp_def] using hh

omit [IsProbabilityMeasure ν] in
include hf hmap in
theorem iIndep_pullback {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {X : ∀ i, Ω' → α i}
    (hX : ∀ i, Measurable (X i)) (h : iIndepFun X ν) :
    iIndepFun (fun i ↦ X i ∘ f) μ := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hX i |>.comp hf).aemeasurable)).mpr
  have hh := h.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable)
  rw [← hmap] at hh
  simpa only [Measure.map_map (Measurable.of_eval hX) hf,
    Measure.map_map (hX _) hf, Function.comp_def] using hh

end Pullback

end Disjointness.FiniteLaw
