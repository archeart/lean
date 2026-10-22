module

public import BBCR.InformationChain
public import Disjointness.InformationCost

/-! Information chain rules for actual variable-length transcripts. Optional
next bits record termination, so padding is not silently charged as communication. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace BBCR

instance optionBitMeasurableSpace : MeasurableSpace (Option Bool) := ⊤
instance optionBitDiscreteMeasurableSpace : DiscreteMeasurableSpace (Option Bool) :=
  ⟨fun _ ↦ trivial⟩

variable {Ω A : Type*} [Fintype Ω] [Fintype A]
  [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]

local instance transcriptChainFiniteRange {E F : Type*} [Finite E] (f : E → F) : FiniteRange f :=
  ⟨Set.finite_range f⟩

theorem information_of_mutually_determined {B C : Type*} [Countable B] [Countable C]
    [MeasurableSpace B] [DiscreteMeasurableSpace B]
    [MeasurableSpace C] [DiscreteMeasurableSpace C]
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (X : Ω → A)
    (U : Ω → B) (V : Ω → C) (f : B → C) (g : C → B)
    (hV : V = f ∘ U) (hU : U = g ∘ V) : mutualInfo X U μ = mutualInfo X V μ := by
  have hUV : condEntropy X U μ ≤ condEntropy X V μ := by
    rw [hV]
    exact condEntropy_comp_ge μ (show Measurable U from .of_discrete)
      (show Measurable X from .of_discrete) f
  have hVU : condEntropy X V μ ≤ condEntropy X U μ := by
    rw [hU]
    exact condEntropy_comp_ge μ (show Measurable V from .of_discrete)
      (show Measurable X from .of_discrete) g
  rw [mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete,
    mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete]
  linarith

noncomputable def transcriptStepInformation (μ : Measure Ω) (X : Ω → A)
    (T : Ω → List Bool) (k : ℕ) : ℝ :=
  condMutualInfo X (fun ω ↦ (T ω)[k]?) (fun ω ↦ (T ω).take k) μ

theorem information_take_succ (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (X : Ω → A) (T : Ω → List Bool) (k : ℕ) :
    mutualInfo X (fun ω ↦ (T ω).take (k + 1)) μ =
      mutualInfo X (fun ω ↦ (T ω).take k) μ + transcriptStepInformation μ X T k := by
  let f : List Bool → List Bool × Option Bool := fun l ↦ (l.take k, l[k]?)
  let g : List Bool × Option Bool → List Bool := fun z ↦ z.1 ++ z.2.toList
  have hf : (fun ω ↦ ((T ω).take k, (T ω)[k]?)) =
      f ∘ (fun ω ↦ (T ω).take (k + 1)) := by
    funext ω
    simp [f, List.take_take, List.getElem?_take_of_lt (Nat.lt_succ_self k)]
  have hg : (fun ω ↦ (T ω).take (k + 1)) =
      g ∘ (fun ω ↦ ((T ω).take k, (T ω)[k]?)) := by
    funext ω
    exact List.take_add_one
  rw [information_of_mutually_determined μ X _ _ f g hf hg, information_chain]
  rfl

/-- Exact message-by-message information accounting, also for transcripts
shorter than the chosen cutoff. -/
theorem information_take_chain (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (X : Ω → A) (T : Ω → List Bool) (n : ℕ) :
    mutualInfo X (fun ω ↦ (T ω).take n) μ =
      ∑ k ∈ Finset.range n, transcriptStepInformation μ X T k := by
  induction n with
  | zero =>
    simp only [List.take_zero, Finset.range_zero, Finset.sum_empty]
    exact mutualInfo_const (show Measurable X from .of_discrete) []
  | succ n ih => rw [information_take_succ, ih, Finset.sum_range_succ]

theorem information_take_interval (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (X : Ω → A) (T : Ω → List Bool) (i j : ℕ) (hij : i ≤ j) :
    mutualInfo X (fun ω ↦ (T ω).take j) μ =
      mutualInfo X (fun ω ↦ (T ω).take i) μ +
        ∑ k ∈ Finset.Ico i j, transcriptStepInformation μ X T k := by
  rw [information_take_chain, information_take_chain]
  exact (Finset.sum_range_add_sum_Ico _ hij).symm

/-- The interval chain rule after fixing an initial prefix. The initial prefix
has zero information under this conditional law. Null prefixes are also covered
because the conditional measure is then zero. -/
theorem information_interval_given_prefix (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (T : Ω → List Bool) (i j : ℕ) (hij : i ≤ j) (s : List Bool) :
    let ν := μ[|(fun ω ↦ (T ω).take i) ⁻¹' {s}]
    (∑ k ∈ Finset.Ico i j, transcriptStepInformation ν X T k) =
      mutualInfo X (fun ω ↦ (T ω).take j) ν := by
  let ν := μ[|(fun ω ↦ (T ω).take i) ⁻¹' {s}]
  have hh : (fun ω ↦ (T ω).take i) =ᵐ[ν] (fun _ ↦ s) :=
    ae_cond_of_forall_mem (show MeasurableSet ((fun ω ↦ (T ω).take i) ⁻¹' {s}) from .of_discrete)
      (fun ω h ↦ h)
  have hpair : (fun ω ↦ (X ω, (T ω).take i)) =ᵐ[ν] (fun ω ↦ (X ω, s)) :=
    hh.mono (fun _ h ↦ Prod.ext rfl h)
  have hid : IdentDistrib (fun ω ↦ (X ω, (T ω).take i)) (fun ω ↦ (X ω, s)) ν ν :=
    IdentDistrib.of_ae_eq (.of_discrete) hpair
  have hzero : mutualInfo X (fun ω ↦ (T ω).take i) ν = 0 := by
    rw [hid.mutualInfo_eq]
    exact mutualInfo_const (show Measurable X from .of_discrete) s
  have h := information_take_interval ν X T i j hij
  rw [hzero, zero_add] at h
  exact h.symm

end BBCR
