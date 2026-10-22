module

public import BBCR.ProtocolFrontier
public import BBCR.SmoothDivergence
public import BBCR.TwoPartyRejection

/-! The rejection-sampling algebra on the actual finite divergence frontier.
Factorization and positive observer masses are proved here. FrontierLikelihood
and FrontierSampling discharge the bad-mass bound in subsequent modules. -/

@[expose] public section

open Disjointness Disjointness.Hellinger

namespace BBCR.ProtocolFrontier

open Prefix

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

abbrev Alphabet (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) :=
  ↥(StoppingFrontier.paths (p.tree r).depth (halt p μ r v xy β) v)

noncomputable def observerFinite (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) : PMF (Alphabet p μ r v xy β) :=
  StoppingFrontier.finiteLaw (p.tree r).depth (halt p μ r v xy β) (Prior.observerNext p μ r) v

noncomputable def aliceFinite (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) : PMF (Alphabet p μ r v xy β) :=
  StoppingFrontier.finiteLaw (p.tree r).depth (halt p μ r v xy β) (aliceKernel p μ r xy.1) v

noncomputable def bobFinite (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) : PMF (Alphabet p μ r v xy β) :=
  StoppingFrontier.finiteLaw (p.tree r).depth (halt p μ r v xy β) (bobKernel p μ r xy.2) v

noncomputable def targetFinite (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) : PMF (Alphabet p μ r v xy β) :=
  StoppingFrontier.finiteLaw (p.tree r).depth (halt p μ r v xy β) (targetKernel p μ r xy) v

theorem finite_factorization (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (w : Alphabet p μ r v xy β) :
    mass (aliceFinite p μ r v xy β) w * mass (bobFinite p μ r v xy β) w =
      mass (observerFinite p μ r v xy β) w * mass (targetFinite p μ r v xy β) w :=
  law_factorization p μ r v xy β w.1

/-- Strict smoothness gives positive observer probability on every atom of the
common frontier. Only actually reached prefixes are used to propagate it. -/
theorem observer_positive (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β ε : ℝ) (hsm : Smooth p ε) (hε : ε < 1 / 2)
    (hv : 0 < Prior.prefixMass p μ r v) (w : Alphabet p μ r v xy β) :
    0 < mass (observerFinite p μ r v xy β) w := by
  apply StoppingFrontier.mass_law_pos _ _ _ (Prior.prefixMass p μ r) _ _ v w.1 hv w.2
  · intro s hs b
    obtain ⟨who,howner⟩ := active_of_not_halt p μ r v xy β s hs
    exact weighted_observerKernel p μ r s who howner b
  · intro s hs hp b
    obtain ⟨who,howner⟩ := active_of_not_halt p μ r v xy β s hs
    have hl := (Prior.observerNext_mass_mem p μ ε hsm r s who howner hp b).1
    linarith

/-- The acceptance-rate estimate now applies to the concrete frontier laws;
its old factorization and observer-positivity hypotheses are discharged. -/
theorem rejection_rate_lower (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β ε : ℝ) (hsm : Smooth p ε) (hε : ε < 1 / 2)
    (hv : 0 < Prior.prefixMass p μ r v) (t : ℝ) (ht : 0 < t) :
    let C := observerFinite p μ r v xy β
    let P := aliceFinite p μ r v xy β
    let Q := bobFinite p μ r v xy β
    let D := targetFinite p μ r v xy β
    (1 / t ^ 2) * (1 - TwoPartyRejection.badMass C P Q D t) ≤
      Rejection.rate C (TwoPartyRejection.acceptWeight C P Q t) :=
  TwoPartyRejection.rate_lower _ _ _ _ t ht (observer_positive p μ r v xy β ε hsm hε hv)
    (finite_factorization p μ r v xy β)

/-- Conditional distortion for the accepted sampling law on this actual
frontier. This algebraic layer retains an explicit bad-mass hypothesis;
FrontierSampling proves the bound, and FrontierTrial implements one trial. -/
theorem rejection_accepted_close (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β ε : ℝ) (hsm : Smooth p ε) (hε : ε < 1 / 2)
    (hv : 0 < Prior.prefixMass p μ r v) (t : ℝ) (ht : 0 < t)
    (hbad : TwoPartyRejection.badMass (observerFinite p μ r v xy β)
      (aliceFinite p μ r v xy β) (bobFinite p μ r v xy β) (targetFinite p μ r v xy β) t < 1) :
    let C := observerFinite p μ r v xy β
    let P := aliceFinite p μ r v xy β
    let Q := bobFinite p μ r v xy β
    let D := targetFinite p μ r v xy β
    let hC := observer_positive p μ r v xy β ε hsm hε hv
    let hf := finite_factorization p μ r v xy β
    let hp := TwoPartyRejection.rate_pos C P Q D t ht hC hf hbad
    variation (Rejection.accepted C (TwoPartyRejection.acceptWeight C P Q t)
      (TwoPartyRejection.accept_nonneg C P Q t ht) hp) D ≤ TwoPartyRejection.badMass C P Q D t :=
  TwoPartyRejection.accepted_close _ _ _ _ t ht (observer_positive p μ r v xy β ε hsm hε hv)
    (finite_factorization p μ r v xy β) hbad

end BBCR.ProtocolFrontier
