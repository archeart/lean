module

public import BBCR.FiniteInformation

/-! Conditional KL accounting and the information chain rule. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger

namespace BBCR

section Conditional

variable {D A B : Type*} [Fintype D] [Fintype A] [Fintype B]
  [MeasurableSpace D] [DiscreteMeasurableSpace D]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [MeasurableSpace B] [DiscreteMeasurableSpace B]

/-- Information of a channel whose input law and kernel depend on public history. -/
noncomputable def conditionalInformation (w : PMF D) (q : D → PMF A)
    (K : D → A → PMF B) : ℝ :=
  ∑ d, mass w d * Disjointness.Channel.information (q d) (K d)

theorem conditionalInformation_eq_condMutualInfo (w : PMF D) (q : D → PMF A)
    (K : D → A → PMF B) :
    conditionalInformation w q K =
      condMutualInfo (fun s : D × (A × B) ↦ s.2.1) (fun s ↦ s.2.2) Prod.fst
        (joint w (fun d ↦ joint (q d) (K d))).toMeasure := by
  rw [condMutualInfo_eq_sum' measurable_fst]
  unfold conditionalInformation
  apply Finset.sum_congr rfl
  intro d _
  simp only [measureReal_def, joint_fiber]
  by_cases hd : w d = 0
  · simp [hd, mass]
  · rw [joint_cond_fst _ _ _ hd, joint_const_toMeasure]
    congr 1
    apply IdentDistrib.mutualInfo_eq
    refine ⟨.of_discrete, .of_discrete, ?_⟩
    change (joint (q d) (K d)).toMeasure.map id =
      ((PMF.pure d).toMeasure.prod (joint (q d) (K d)).toMeasure).map Prod.snd
    simp

omit [MeasurableSpace D] [DiscreteMeasurableSpace D] in
/-- Conditional form of the finite information/divergence identity, including
zero-mass histories and zero-mass input fibers. -/
theorem conditionalInformation_eq_average_divergence (w : PMF D) (q : D → PMF A)
    (K : D → A → PMF B) :
    conditionalInformation w q K =
      ∑ d, mass w d * ∑ a, mass (q d) a * divergence (K d a) ((q d).bind (K d)) := by
  simp only [conditionalInformation, information_eq_average_divergence]

end Conditional

section Chain

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Countable B] [Countable C]
  [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [MeasurableSpace B] [DiscreteMeasurableSpace B]
  [MeasurableSpace C] [DiscreteMeasurableSpace C]

local instance chainFiniteRange {E F : Type*} [Finite E] (f : E → F) : FiniteRange f :=
  ⟨Set.finite_range f⟩

theorem information_chain (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (X : Ω → A) (U : Ω → B) (V : Ω → C) :
    mutualInfo X (fun ω ↦ (U ω, V ω)) μ =
      mutualInfo X U μ + condMutualInfo X V U μ := by
  rw [mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete,
    mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete,
    condMutualInfo_eq' .of_discrete .of_discrete .of_discrete]
  have hswap := condEntropy_of_injective' μ
    (show Measurable X from .of_discrete)
    (show Measurable (fun ω ↦ (V ω, U ω)) from .of_discrete)
    Prod.swap Prod.swap_injective
    (show Measurable (Prod.swap ∘ fun ω ↦ (V ω, U ω)) from .of_discrete)
  change condEntropy X (fun ω ↦ (U ω, V ω)) μ =
    condEntropy X (fun ω ↦ (V ω, U ω)) μ at hswap
  rw [hswap]
  ring

end Chain

section VectorChain

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
  [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [MeasurableSpace B] [DiscreteMeasurableSpace B]

local instance vectorFiniteRange {E F : Type*} [Finite E] (f : E → F) : FiniteRange f :=
  ⟨Set.finite_range f⟩

noncomputable def vectorStepInformation (μ : Measure Ω) {n : ℕ}
    (X : Ω → A) (T : Fin n → Ω → B) (i : Fin n) : ℝ :=
  condMutualInfo X (T i) (fun ω (j : Fin i.val) ↦ T ⟨j.val, j.isLt.trans i.isLt⟩ ω) μ

/-- The transcript's information is exactly the sum of conditional next-message
information. This is the chain-rule part of BBCR Lemma 8.2. -/
theorem information_vector_chain (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Ω → A) (T : Fin n → Ω → B) :
    mutualInfo X (fun ω i ↦ T i ω) μ = ∑ i, vectorStepInformation μ X T i := by
  induction n with
  | zero =>
    have he : (fun ω i ↦ T i ω) = (fun _ : Ω ↦ (Fin.elim0 : Fin 0 → B)) := by
      funext ω i
      exact Fin.elim0 i
    rw [he]
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact mutualInfo_const (μ := μ) (show Measurable X from .of_discrete) Fin.elim0
  | succ n ih =>
    let f : (Fin (n + 1) → B) → (Fin n → B) × B :=
      fun t ↦ (fun i ↦ t i.castSucc, t (Fin.last n))
    have hf : Function.Injective f := by
      intro t u h
      ext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact congrFun (congrArg Prod.fst h) j
      · exact congrArg Prod.snd h
    have hcond := condEntropy_of_injective' μ
      (show Measurable X from .of_discrete)
      (show Measurable (fun ω i ↦ T i ω) from .of_discrete) f hf
      (show Measurable (f ∘ fun ω i ↦ T i ω) from .of_discrete)
    have he : mutualInfo X (fun ω i ↦ T i ω) μ =
        mutualInfo X (fun ω ↦ (fun i : Fin n ↦ T i.castSucc ω, T (Fin.last n) ω)) μ := by
      rw [mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete,
        mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete]
      exact congrArg (fun z ↦ entropy X μ - z) hcond.symm
    rw [he, information_chain, ih, Fin.sum_univ_castSucc]
    congr 1

end VectorChain
end BBCR
