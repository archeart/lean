module

public import BBCR.NoisyInformation
public import BBCR.PublicInformation
public import BBCR.SmoothingProtocol

/-! Information comparison for the actual noisy-block protocol. The good event
concerns the independent correctness tapes, rather than a conditional
independence assumption about the protocol's persistent private seeds. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger
open scoped Classical

namespace BBCR.SmoothingProtocol

open SmoothingTree

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R]
  [Fintype SA] [Fintype SB]

abbrev NoisePair (C m : ℕ) := Tape C m × Tape C m

noncomputable def noisePairLaw {C m : ℕ} (η : PMF (Tape C m)) : PMF (NoisePair C m) :=
  joint η (fun _ ↦ η)

noncomputable def goodFlag {C m : ℕ} (n : NoisePair C m) : Bool :=
  decide (GoodTape n.1 ∧ GoodTape n.2)

/-- Separate the original input/private-seed experiment from the new noise. -/
def regroup (p : Protocol X Y R SA SB) (m : ℕ) :
    Prefix.Prior.Sample X Y (SA × Tape p.cost m) (SB × Tape p.cost m) ≃
      Prefix.Prior.Sample X Y SA SB × NoisePair p.cost m where
  toFun ω := ((ω.1,ω.2.1.1,ω.2.2.1),ω.2.1.2,ω.2.2.2)
  invFun z := (z.1.1,(z.1.2.1,z.2.1),(z.1.2.2,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem execution_regroup (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (η : PMF (Tape p.cost m)) :
    (Prefix.Prior.execution (protocol p m η) μ).map (regroup p m) =
      joint (Prefix.Prior.execution p μ) (fun _ ↦ noisePairLaw η) := by
  apply PMF.ext
  rintro ⟨⟨xy,sa,sb⟩,ta,tb⟩
  rw [map_equiv_apply]
  simp only [regroup, Equiv.coe_fn_symm_mk, Prefix.Prior.execution,
    Prefix.Experiment.privateSeeds, protocol, noisePairLaw, joint_apply]
  ring

noncomputable def noisyExecution (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (η : PMF (Tape p.cost m)) :
    PMF (Prefix.Prior.Sample X Y SA SB × NoisePair p.cost m) :=
  joint (Prefix.Prior.execution p μ) (fun _ ↦ noisePairLaw η)

noncomputable def noisyTranscript (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m))
    (r : R) (z : Prefix.Prior.Sample X Y SA SB × NoisePair p.cost m) : List Bool :=
  Prefix.Experiment.transcript (protocol p m η) r z.1.1.1 z.1.1.2
    ((z.1.2.1,z.2.1),(z.1.2.2,z.2.2))

def originalTranscript (p : Protocol X Y R SA SB) (r : R)
    (ω : Prefix.Prior.Sample X Y SA SB) : ↥(p.tree r).leafPaths :=
  ⟨Prefix.Experiment.transcript p r ω.1.1 ω.1.2 ω.2,
    Tree.run_mem_leafPaths _ _ _⟩

omit [Fintype X] [Fintype Y] in
theorem noisyTranscript_of_good (p : Protocol X Y R SA SB) (m : ℕ)
    (η : PMF (Tape p.cost m)) (r : R)
    (z : Prefix.Prior.Sample X Y SA SB × NoisePair p.cost m) (h : goodFlag z.2 = true) :
    noisyTranscript p m η r z =
      encodedTrace p.cost m 0 (p.tree r) (originalTranscript p r z.1).1 z.2.1 z.2.2 := by
  have hg : GoodTape z.2.1 ∧ GoodTape z.2.2 := by simpa only [goodFlag, decide_eq_true_eq] using h
  simpa only [noisyTranscript, Prefix.Experiment.transcript, protocol, Tree.run_comap,
    originalTranscript] using run_encodedTrace_of_good p.cost m 0 (p.tree r)
      (z.1.1.1,z.1.2.1) (z.1.1.2,z.1.2.2) z.2.1 z.2.2 hg.1 hg.2

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

local instance smoothingInformationFiniteRange {E F : Type*} [Finite E] (f : E → F) :
    FiniteRange f := ⟨Set.finite_range f⟩

omit [Fintype R] in
/-- The finite leaf-path subtype carries exactly the original transcript's
information; its proof of membership carries no extra information. -/
theorem originalTranscript_information (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) (r : R) :
    mutualInfo Prod.fst (originalTranscript p r) (Prefix.Prior.execution p μ).toMeasure =
      mutualInfo Prod.fst (fun ω ↦ Prefix.Experiment.transcript p r ω.1.1 ω.1.2 ω.2)
        (Prefix.Prior.execution p μ).toMeasure := by
  have hc := condEntropy_of_injective' (Prefix.Prior.execution p μ).toMeasure
    (show Measurable (Prod.fst : Prefix.Prior.Sample X Y SA SB → X × Y) from .of_discrete)
    (show Measurable (originalTranscript p r) from .of_discrete)
    Subtype.val Subtype.val_injective (.of_discrete)
  rw [mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete,
    mutualInfo_eq_entropy_sub_condEntropy .of_discrete .of_discrete]
  exact congrArg (fun h ↦ entropy Prod.fst (Prefix.Prior.execution p μ).toMeasure - h) hc.symm

/-- On the independent event that both full correctness tapes are good, the
physical smoothed transcript has at most the original information, for every
fixed public seed. Null good events are included. -/
theorem good_event_information_le (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (η : PMF (Tape p.cost m)) (r : R) :
    mutualInfo (fun z : Prefix.Prior.Sample X Y SA SB × NoisePair p.cost m ↦ z.1.1)
      (noisyTranscript p m η r)
      ((noisyExecution p μ m η).toMeasure[|(goodFlag ∘ Prod.snd) ⁻¹' {true}]) ≤
        mutualInfo Prod.fst (fun ω ↦ Prefix.Experiment.transcript p r ω.1.1 ω.1.2 ω.2)
          (Prefix.Prior.execution p μ).toMeasure := by
  rw [← originalTranscript_information]
  exact noise_conditioned_information_le (Prefix.Prior.execution p μ) (noisePairLaw η)
    Prod.fst (originalTranscript p r) (noisyTranscript p m η r) goodFlag
    (fun z ↦ encodedTrace p.cost m 0 (p.tree r) z.1.1 z.2.1 z.2.2)
    (noisyTranscript_of_good p m η r)

/-- Bad executions are controlled by the actual physical tree's communication,
without charging for any of the private or public seed alphabets. -/
theorem bad_event_information_le (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (η : PMF (Tape p.cost m)) (r : R) :
    mutualInfo (fun z : Prefix.Prior.Sample X Y SA SB × NoisePair p.cost m ↦ z.1.1)
      (noisyTranscript p m η r)
      ((noisyExecution p μ m η).toMeasure[|(goodFlag ∘ Prod.snd) ⁻¹' {false}]) ≤
        ((m * p.cost : ℕ) : ℝ) * Real.log 2 := by
  apply information_le_of_support _ _ _ ((protocol p m η).tree r).leafPaths (m * p.cost)
  · exact Filter.Eventually.of_forall fun z ↦ Tree.run_mem_leafPaths _ _ _
  · refine (Tree.card_leafPaths_le _).trans ?_
    have hd := ((protocol p m η).depth_le_cost r).trans (cost_le p m η)
    gcongr

noncomputable def badNoiseProbability {C m : ℕ} (η : PMF (Tape C m)) : ℝ :=
  mass ((noisePairLaw η).map goodFlag) false

theorem badNoiseProbability_eq_probability {C m : ℕ} (η : PMF (Tape C m)) :
    badNoiseProbability η =
      probability (noisePairLaw η) (fun n ↦ ¬GoodTape n.1 ∨ ¬GoodTape n.2) := by
  rw [badNoiseProbability, mass_map_sum, probability]
  apply Finset.sum_congr rfl
  intro n _
  by_cases ha : GoodTape n.1 <;> by_cases hb : GoodTape n.2 <;> simp [goodFlag, ha, hb]

theorem badNoiseProbability_le {C m : ℕ} (η : PMF (Tape C m)) :
    badNoiseProbability η ≤ 2 * probability η (fun tape ↦ ¬GoodTape tape) := by
  rw [badNoiseProbability_eq_probability]
  refine (probability_or_le _ _ _).trans ?_
  have ha := probability_map (noisePairLaw η) Prod.fst (fun tape ↦ ¬GoodTape tape)
  have hb := probability_map (noisePairLaw η) Prod.snd (fun tape ↦ ¬GoodTape tape)
  rw [noisePairLaw, joint_map_fst] at ha
  rw [noisePairLaw, Disjointness.Channel.joint_map_snd, PMF.bind_const] at hb
  dsimp only [noisePairLaw]
  rw [← ha, ← hb]
  exact le_of_eq (by ring)

theorem information_eq_noisyExecution (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (η : PMF (Tape p.cost m)) (r : R) :
    mutualInfo Prod.fst
      (fun ω ↦ Prefix.Experiment.transcript (protocol p m η) r ω.1.1 ω.1.2 ω.2)
      (Prefix.Prior.execution (protocol p m η) μ).toMeasure =
        mutualInfo (fun z : Prefix.Prior.Sample X Y SA SB × NoisePair p.cost m ↦ z.1.1)
          (noisyTranscript p m η r) (noisyExecution p μ m η).toMeasure := by
  apply IdentDistrib.mutualInfo_eq
  refine ⟨.of_discrete, .of_discrete, ?_⟩
  have hm : (Prefix.Prior.execution (protocol p m η) μ).toMeasure.map (regroup p m) =
      (noisyExecution p μ m η).toMeasure := by
    rw [PMF.toMeasure_map _ _ (.of_discrete), execution_regroup]
    rfl
  have hh := congrArg (fun ν ↦ ν.map (fun z ↦ (z.1.1,noisyTranscript p m η r z))) hm
  rw [Measure.map_map (.of_discrete) (.of_discrete)] at hh
  exact hh

/-- Fixed-public-seed information inflation. The good flag is independent of
the input, so revealing it incurs no entropy penalty. -/
theorem information_le_original_add_bad (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (η : PMF (Tape p.cost m)) (r : R) :
    mutualInfo Prod.fst
      (fun ω ↦ Prefix.Experiment.transcript (protocol p m η) r ω.1.1 ω.1.2 ω.2)
      (Prefix.Prior.execution (protocol p m η) μ).toMeasure ≤
        mutualInfo Prod.fst (fun ω ↦ Prefix.Experiment.transcript p r ω.1.1 ω.1.2 ω.2)
          (Prefix.Prior.execution p μ).toMeasure +
            badNoiseProbability η * ((m * p.cost : ℕ) : ℝ) * Real.log 2 := by
  rw [information_eq_noisyExecution]
  let ν := (noisyExecution p μ m η).toMeasure
  let flag : Prefix.Prior.Sample X Y SA SB × NoisePair p.cost m → Bool := goodFlag ∘ Prod.snd
  have hind : IndepFun (fun z : Prefix.Prior.Sample X Y SA SB × NoisePair p.cost m ↦ z.1.1)
      flag ν := by
    have hi : IndepFun Prod.fst Prod.snd ν := by
      dsimp only [ν, noisyExecution]
      rw [joint_const_toMeasure]
      exact indepFun_fst_snd
    exact hi.comp (show Measurable (Prod.fst : Prefix.Prior.Sample X Y SA SB → X × Y)
      from .of_discrete) (show Measurable goodFlag from .of_discrete)
  have hm (b : Bool) : ν.real (flag ⁻¹' {b}) = mass ((noisePairLaw η).map goodFlag) b := by
    rw [measureReal_def, FiniteCondition.fiber_measure]
    change mass ((noisyExecution p μ m η).map (goodFlag ∘ Prod.snd)) b = _
    rw [← PMF.map_comp, noisyExecution, Disjointness.Channel.joint_map_snd, PMF.bind_const]
  have hg := good_event_information_le p μ m η r
  have hb := bad_event_information_le p μ m η r
  have hh := information_le_flag_average ν
    (fun z : Prefix.Prior.Sample X Y SA SB × NoisePair p.cost m ↦ z.1.1)
    (noisyTranscript p m η r) flag hind
  refine hh.trans ?_
  have hI := mutualInfo_nonneg
    (show Measurable (Prod.fst : Prefix.Prior.Sample X Y SA SB → X × Y) from .of_discrete)
    (show Measurable (fun ω ↦ Prefix.Experiment.transcript p r ω.1.1 ω.1.2 ω.2) from .of_discrete)
    (Prefix.Prior.execution p μ).toMeasure
  have hgle : mass ((noisePairLaw η).map goodFlag) true ≤ 1 := by
    have hs := sum_mass ((noisePairLaw η).map goodFlag)
    rw [Fintype.sum_bool] at hs
    linarith [mass_nonneg ((noisePairLaw η).map goodFlag) false]
  calc
    _ ≤ ν.real (flag ⁻¹' {true}) *
          mutualInfo Prod.fst (fun ω ↦ Prefix.Experiment.transcript p r ω.1.1 ω.1.2 ω.2)
            (Prefix.Prior.execution p μ).toMeasure +
        ν.real (flag ⁻¹' {false}) * (((m * p.cost : ℕ) : ℝ) * Real.log 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hg measureReal_nonneg)
        (mul_le_mul_of_nonneg_left hb measureReal_nonneg)
    _ ≤ _ := by
      rw [hm true, hm false]
      have hi := mul_le_mul_of_nonneg_right hgle hI
      dsimp only [badNoiseProbability]
      nlinarith

variable [MeasurableSpace R] [DiscreteMeasurableSpace R]

/-- Information inflation for the same actual private-randomness protocol that
has the checked cost, fidelity, and smoothness guarantees. -/
theorem externalInformation_le_original_add_bad (p : Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (m : ℕ) (η : PMF (Tape p.cost m)) :
    externalInformation (protocol p m η) μ ≤ externalInformation p μ +
      badNoiseProbability η * ((m * p.cost : ℕ) : ℝ) * Real.log 2 := by
  rw [externalInformation_eq_public_average, externalInformation_eq_public_average]
  calc
    _ ≤ ∑ r, mass p.publicLaw r *
      (mutualInfo Prod.fst (fun ω ↦ Prefix.Experiment.transcript p r ω.1.1 ω.1.2 ω.2)
        (Prefix.Prior.execution p μ).toMeasure +
          badNoiseProbability η * ((m * p.cost : ℕ) : ℝ) * Real.log 2) :=
      Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_left
        (information_le_original_add_bad p μ m η r) (mass_nonneg p.publicLaw r)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_mass, one_mul]

end BBCR.SmoothingProtocol
