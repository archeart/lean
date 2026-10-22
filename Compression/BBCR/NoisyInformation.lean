module

public import BBCR.NoiseResampling
public import BBCR.InformationChain

/-! Data processing under independent noise, also after conditioning on a noise
event, and information bounds for good/bad-event decompositions. These include
the single-block inequality (8.3) and the tools for whole-tape smoothing. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.FiniteLaw

namespace BBCR

variable {A B N C : Type*} [Fintype A] [Fintype B] [Fintype N] [Countable C]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [MeasurableSpace B] [DiscreteMeasurableSpace B]
  [MeasurableSpace N] [DiscreteMeasurableSpace N]
  [MeasurableSpace C] [DiscreteMeasurableSpace C]

local instance noisyInformationFiniteRange {E F : Type*} [Finite E] (f : E → F) : FiniteRange f :=
  ⟨Set.finite_range f⟩

/-- The joint input/intended-message law is arbitrary. Independence of the
extra noise is established by the actual product construction. -/
theorem independent_randomization_information_le (w : PMF (A × B)) (η : PMF N) (f : B × N → C) :
    mutualInfo (fun z : (A × B) × N ↦ z.1.1) (fun z ↦ f (z.1.2,z.2))
      (joint w (fun _ ↦ η)).toMeasure ≤ mutualInfo Prod.fst Prod.snd w.toMeasure := by
  let ν := (joint w (fun _ ↦ η)).toMeasure
  have hind : IndepFun (fun z : (A × B) × N ↦ (z.1.1,z.1.2)) Prod.snd ν := by
    change IndepFun Prod.fst Prod.snd ν
    dsimp only [ν]
    rw [joint_const_toMeasure]
    exact indepFun_fst_snd
  have hc := condEntropy_prod_eq_of_indepFun
    (X := fun z : (A × B) × N ↦ z.1.1) (Y := fun z ↦ z.1.2) (Z := Prod.snd)
    (show Measurable (fun z : (A × B) × N ↦ z.1.1) from .of_discrete)
    (show Measurable (fun z : (A × B) × N ↦ z.1.2) from .of_discrete)
    (.of_discrete) hind
  let : FiniteRange (fun z : (A × B) × N ↦ (z.1.2,z.2)) := ⟨Set.finite_range _⟩
  have hfull : mutualInfo (fun z : (A × B) × N ↦ z.1.1) (fun z ↦ (z.1.2,z.2)) ν =
      mutualInfo (fun z : (A × B) × N ↦ z.1.1) (fun z ↦ z.1.2) ν := by
    rw [mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete,
      mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete, hc]
  have hid : IdentDistrib (fun z : (A × B) × N ↦ (z.1.1,z.1.2)) id ν w.toMeasure := by
    refine ⟨.of_discrete, .of_discrete, ?_⟩
    change (joint w (fun _ ↦ η)).toMeasure.map Prod.fst = w.toMeasure.map id
    rw [PMF.toMeasure_map _ _ (.of_discrete), joint_map_fst, Measure.map_id]
  have hd := mutual_comp_comp_le (X := fun z : (A × B) × N ↦ z.1.1)
    (Y := fun z ↦ (z.1.2,z.2)) ν (.of_discrete) (.of_discrete) id f (.of_discrete)
  simpa only [Function.comp_def, id_eq, hfull, hid.mutualInfo_eq] using hd

/-- Conditioning on an event of the independent noise leaves the original
experiment unchanged. Any observation that factors through the intended
transcript and noise on that event has at most the original information.
The assertion also covers an event of probability zero. -/
theorem noise_conditioned_information_le {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (w : PMF Ω) (η : PMF N) (X : Ω → A) (T : Ω → B)
    (Y : Ω × N → C) (flag : N → Bool) (f : B × N → C)
    (hfactor : ∀ z, flag z.2 = true → Y z = f (T z.1,z.2)) :
    mutualInfo (fun z : Ω × N ↦ X z.1) Y
      ((joint w (fun _ ↦ η)).toMeasure[|(flag ∘ Prod.snd) ⁻¹' {true}]) ≤
        mutualInfo X T w.toMeasure := by
  let ν := (joint w (fun _ ↦ η)).toMeasure
  let E : Set (Ω × N) := (flag ∘ Prod.snd) ⁻¹' {true}
  have hind : IndepFun Prod.fst Prod.snd ν := by
    dsimp only [ν]
    rw [joint_const_toMeasure]
    exact indepFun_fst_snd
  have hpair := hind.comp
    (show Measurable (fun ω ↦ (X ω,T ω)) from .of_discrete)
    (show Measurable (id : N → N) from .of_discrete)
  change IndepFun (fun z : Ω × N ↦ (X z.1,T z.1)) Prod.snd ν at hpair
  have hflag := hpair.comp (show Measurable (id : A × B → A × B) from .of_discrete)
    (show Measurable flag from .of_discrete)
  change IndepFun (fun z : Ω × N ↦ (X z.1,T z.1)) (flag ∘ Prod.snd) ν at hflag
  by_cases hnull : ν E = 0
  · rw [show ν[|E] = 0 from cond_eq_zero_of_meas_eq_zero hnull]
    simpa [mutualInfo_def] using mutualInfo_nonneg (show Measurable X from .of_discrete)
      (show Measurable T from .of_discrete) w.toMeasure
  · have hcond := hpair.cond_right (show MeasurableSet (flag ⁻¹' {true}) from .of_discrete)
        (show Measurable (Prod.snd : Ω × N → N) from .of_discrete)
    let : IsProbabilityMeasure (ν[|E]) := cond_isProbabilityMeasure hnull
    change IndepFun (fun z : Ω × N ↦ (X z.1,T z.1)) Prod.snd (ν[|E]) at hcond
    have hc := condEntropy_prod_eq_of_indepFun
      (X := fun z : Ω × N ↦ X z.1) (Y := fun z ↦ T z.1) (Z := Prod.snd)
      (show Measurable (fun z : Ω × N ↦ X z.1) from .of_discrete)
      (show Measurable (fun z : Ω × N ↦ T z.1) from .of_discrete)
      (.of_discrete) hcond
    let : FiniteRange (fun z : Ω × N ↦ (T z.1,z.2)) := ⟨Set.finite_range _⟩
    have hfull : mutualInfo (fun z : Ω × N ↦ X z.1) (fun z ↦ (T z.1,z.2)) (ν[|E]) =
        mutualInfo (fun z : Ω × N ↦ X z.1) (fun z ↦ T z.1) (ν[|E]) := by
      rw [mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete,
        mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete, hc]
    have hid : IdentDistrib (fun z : Ω × N ↦ (X z.1,T z.1)) (fun ω ↦ (X ω,T ω))
        ν w.toMeasure := by
      refine ⟨.of_discrete, .of_discrete, ?_⟩
      change ν.map ((fun ω ↦ (X ω,T ω)) ∘ Prod.fst) = _
      rw [← Measure.map_map (show Measurable (fun ω ↦ (X ω,T ω)) from .of_discrete)
        (show Measurable (Prod.fst : Ω × N → Ω) from .of_discrete)]
      dsimp only [ν]
      rw [PMF.toMeasure_map _ _ (.of_discrete), joint_map_fst]
    have he : IdentDistrib (fun z : Ω × N ↦ (X z.1,Y z))
        (fun z : Ω × N ↦ (X z.1,f (T z.1,z.2))) (ν[|E]) (ν[|E]) :=
      IdentDistrib.of_ae_eq (.of_discrete)
        (ae_cond_of_forall_mem (show MeasurableSet E from .of_discrete)
          (fun z hz ↦ Prod.ext rfl (hfactor z hz)))
    rw [he.mutualInfo_eq]
    have hd := mutual_comp_comp_le (X := fun z : Ω × N ↦ X z.1)
      (Y := fun z ↦ (T z.1,z.2)) (ν[|E]) (.of_discrete) (.of_discrete) id f (.of_discrete)
    change mutualInfo (fun z : Ω × N ↦ X z.1) (fun z ↦ f (T z.1,z.2)) (ν[|E]) ≤ _ at hd
    rw [hfull, ← (hflag.identDistrib_cond (.singleton _) (.of_discrete) (.of_discrete)
      hnull).mutualInfo_eq, hid.mutualInfo_eq] at hd
    exact hd

theorem information_le_flag_average {Ω T : Type*} [Fintype Ω] [Countable T]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    [MeasurableSpace T] [DiscreteMeasurableSpace T]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : Ω → A) (Y : Ω → T) (flag : Ω → Bool)
    (hind : IndepFun X flag ν) :
    mutualInfo X Y ν ≤
      ν.real (flag ⁻¹' {true}) * mutualInfo X Y (ν[|flag ⁻¹' {true}]) +
      ν.real (flag ⁻¹' {false}) * mutualInfo X Y (ν[|flag ⁻¹' {false}]) := by
  have hi := hind.mutualInfo_eq_zero (show Measurable X from .of_discrete) (.of_discrete)
  have hc := information_chain ν X flag Y
  rw [hi, zero_add] at hc
  have hd := mutual_comp_comp_le (X := X) (Y := fun ω ↦ (flag ω,Y ω))
    ν (.of_discrete) (.of_discrete) id Prod.snd (.of_discrete)
  change mutualInfo X Y ν ≤ mutualInfo X (fun ω ↦ (flag ω,Y ω)) ν at hd
  rw [hc, condMutualInfo_eq_sum' (show Measurable flag from .of_discrete), Fintype.sum_bool] at hd
  exact hd

/-- A transcript supported on at most `2^c` paths reveals at most `c log 2`
nats, also under a zero conditional measure. No seed-cardinality bound is used. -/
theorem information_le_of_support {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (ν : Measure Ω) [IsZeroOrProbabilityMeasure ν] (X : Ω → A) (Y : Ω → C)
    (S : Finset C) (c : ℕ) (hmem : ∀ᵐ ω ∂ν, Y ω ∈ S) (hcard : S.card ≤ 2 ^ c) :
    mutualInfo X Y ν ≤ (c : ℝ) * Real.log 2 := by
  rw [mutualInfo_eq_entropy_sub_condEntropy' .of_discrete .of_discrete]
  refine (sub_le_self _ (condEntropy_nonneg _ _ _)).trans ?_
  have he := entropy_le_log_card_of_mem (show Measurable Y from .of_discrete) hmem
  by_cases hz : S.card = 0
  · simp only [hz, Nat.cast_zero, Real.log_zero] at he
    exact he.trans (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
  · refine he.trans ?_
    calc
      Real.log S.card ≤ Real.log ((2 : ℝ) ^ c) :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hcard)
      _ = (c : ℝ) * Real.log 2 := Real.log_pow _ _

end BBCR
