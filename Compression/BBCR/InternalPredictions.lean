module

public import BBCR.InternalAccounting
public import BBCR.ThresholdCoupling

/-! Sender-local predictions and the internal-information charge for mistakes. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.InternalPrediction

open Prefix

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable local instance : DecidableEq (X ⊕ Y) := Classical.decEq _

noncomputable def alice (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (x : X) (s : List Bool) : PMF Bool :=
  match Tree.speaker (p.tree r) s with
  | some .alice => Protocol.aliceNext p r s x
  | some .bob => Prior.observerNext p (alicePrior μ x) r s
  | none => PMF.pure false

noncomputable def bob (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (y : Y) (s : List Bool) : PMF Bool :=
  match Tree.speaker (p.tree r) s with
  | some .alice => Prior.observerNext p (bobPrior μ y) r s
  | some .bob => Protocol.bobNext p r s y
  | none => PMF.pure false

noncomputable def kernels (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (s : List Bool) : X ⊕ Y → PMF Bool := Sum.elim (fun x ↦ alice p μ r x s) (fun y ↦ bob p μ r y s)

noncomputable def coupledNode (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (s : List Bool) : PMF (X ⊕ Y → Bool) := ThresholdCoupling.couple (kernels p μ r s)

theorem coupledNode_marginal (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (s : List Bool) (i : X ⊕ Y) :
    (coupledNode p μ r s).map (fun row ↦ row i) = kernels p μ r s i := ThresholdCoupling.couple_marginal (kernels p μ r s) i

theorem coupledNode_mistake (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (s : List Bool) (x : X) (y : Y) :
    probability (coupledNode p μ r s) (fun row ↦ row (.inl x) ≠ row (.inr y)) =
      variation (alice p μ r x s) (bob p μ r y s) := ThresholdCoupling.couple_disagreement (kernels p μ r s) (.inl x) (.inr y)

variable [Fintype R]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

omit [Fintype R] [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y] [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA] [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem conditioned_execution_support {H : Type} [Fintype H]
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (f : X × Y → H)
    (ω : Prior.Sample X Y SA SB) (hω : mass (Prior.execution p μ) ω ≠ 0) :
    mass (Prior.execution p (FiniteCondition.law μ f (f ω.1))) ω ≠ 0 := by
  have hm : mass (Prior.execution p μ) ω = mass μ ω.1 * mass (Experiment.privateSeeds p) ω.2 := by
    rcases ω with ⟨xy,a,b⟩
    simp [Prior.execution,mass,Disjointness.FiniteLaw.joint_apply]
  have hi := FiniteCondition.own_fiber_support μ f ω.1 ((mul_ne_zero_iff.mp (hm.symm.trans_ne hω)).1)
  have hp := (mul_ne_zero_iff.mp (hm.symm.trans_ne hω)).2
  have he : mass (Prior.execution p (FiniteCondition.law μ f (f ω.1))) ω =
      mass (FiniteCondition.law μ f (f ω.1)) ω.1 * mass (Experiment.privateSeeds p) ω.2 := by
    rcases ω with ⟨xy,a,b⟩
    simp [Prior.execution,mass,Disjointness.FiniteLaw.joint_apply]
  rw [he]
  exact mul_ne_zero hi hp

omit [Fintype R] [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y] [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA] [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
/-- At every actual supported message, squared disagreement is charged to the
sum of the two receiver-conditioned KL costs. -/
theorem mistake_sq_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (k : ℕ) (ω : Prior.Sample X Y SA SB) (hω : mass (Prior.execution p μ) ω ≠ 0) :
    variation (alice p μ r ω.1.1 (Prior.history p r k ω))
      (bob p μ r ω.1.2 (Prior.history p r k ω)) ^ 2 ≤
      Prior.internalNodeDivergence p μ r (Prior.history p r k ω) ω.1 := by
  let s := Prior.history p r k ω
  have ha := Prior.reached_posterior_support p (alicePrior μ ω.1.1) r k ω
    (conditioned_execution_support p μ Prod.fst ω hω)
  have hb := Prior.reached_posterior_support p (bobPrior μ ω.1.2) r k ω
    (conditioned_execution_support p μ Prod.snd ω hω)
  have hna := Prior.nodeDivergence_nonneg p (alicePrior μ ω.1.1) r s ω.1 ha.1 ha.2
  have hnb := Prior.nodeDivergence_nonneg p (bobPrior μ ω.1.2) r s ω.1 hb.1 hb.2
  have hra := Prior.posterior_support_reach_pos p (alicePrior μ ω.1.1) r s ha.1 ω.1 ha.2
  have hrb := Prior.posterior_support_reach_pos p (bobPrior μ ω.1.2) r s hb.1 ω.1 hb.2
  cases hs : Tree.speaker (p.tree r) s with
  | none => simp [alice,bob,hs,variation,Prior.internalNodeDivergence,Prior.nodeDivergence,
      Prior.aliceDivergence,Prior.bobDivergence,s]
  | some who =>
    cases who with
    | alice =>
      have hsup := supported_mixture (Prior.posterior p (bobPrior μ ω.1.2) r s)
        (fun xy ↦ Protocol.next p r xy.1 xy.2 s) ω.1 hb.2
      rw [Protocol.next_eq_alice p r _ _ s hs hrb] at hsup
      have hv := variation_sq_le_divergence _ _ hsup
      change variation (Protocol.aliceNext p r s ω.1.1) (Prior.observerNext p (bobPrior μ ω.1.2) r s) ^ 2 ≤
        divergence (Protocol.aliceNext p r s ω.1.1) (Prior.observerNext p (bobPrior μ ω.1.2) r s) at hv
      have he : Prior.nodeDivergence p (bobPrior μ ω.1.2) r s ω.1 =
          divergence (Protocol.aliceNext p r s ω.1.1) (Prior.observerNext p (bobPrior μ ω.1.2) r s) := by
        simp [Prior.nodeDivergence,Prior.aliceDivergence,Prior.bobDivergence,hs]
      change variation (alice p μ r ω.1.1 s) (bob p μ r ω.1.2 s) ^ 2 ≤
        Prior.nodeDivergence p (alicePrior μ ω.1.1) r s ω.1 + Prior.nodeDivergence p (bobPrior μ ω.1.2) r s ω.1
      simp only [alice,bob,hs]

      rw [← he] at hv
      linarith
    | bob =>
      have hsup := supported_mixture (Prior.posterior p (alicePrior μ ω.1.1) r s)
        (fun xy ↦ Protocol.next p r xy.1 xy.2 s) ω.1 ha.2
      rw [Protocol.next_eq_bob p r _ _ s hs hra] at hsup
      have hv := variation_sq_le_divergence _ _ hsup
      change variation (Protocol.bobNext p r s ω.1.2) (Prior.observerNext p (alicePrior μ ω.1.1) r s) ^ 2 ≤
        divergence (Protocol.bobNext p r s ω.1.2) (Prior.observerNext p (alicePrior μ ω.1.1) r s) at hv
      have he : Prior.nodeDivergence p (alicePrior μ ω.1.1) r s ω.1 =
          divergence (Protocol.bobNext p r s ω.1.2) (Prior.observerNext p (alicePrior μ ω.1.1) r s) := by
        simp [Prior.nodeDivergence,Prior.aliceDivergence,Prior.bobDivergence,hs]
      change variation (alice p μ r ω.1.1 s) (bob p μ r ω.1.2 s) ^ 2 ≤
        Prior.nodeDivergence p (alicePrior μ ω.1.1) r s ω.1 + Prior.nodeDivergence p (bobPrior μ ω.1.2) r s ω.1
      simp only [alice,bob,hs]
      rw [show variation (Prior.observerNext p (alicePrior μ ω.1.1) r s) (Protocol.bobNext p r s ω.1.2) =
        variation (Protocol.bobNext p r s ω.1.2) (Prior.observerNext p (alicePrior μ ω.1.1) r s) by simp only [variation,abs_sub_comm]]
      rw [← he] at hv
      linarith

end BBCR.InternalPrediction
