module

public import BBCR.Simulation
public import BBCR.FiniteInformation

/-! An actual zero-communication, exact simulator when external information is zero. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.Hellinger

namespace BBCR

variable {X Y R SA SB : Type}
  [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]

/-- Publicly sample an original view, transmit no messages, and let both parties
decode the same public sample. This is an actual protocol in the reused model. -/
noncomputable def publicSampler (p : Protocol X Y R SA SB) (q : PMF p.View) : Simulator p where
  publicSeed := p.View
  aliceSeed := Unit
  bobSeed := Unit
  protocol := {
    publicLaw := q
    aliceLaw := PMF.pure ()
    bobLaw := PMF.pure ()
    tree := fun _ ↦ .leaf false }
  aliceDecode _ v := v.1
  bobDecode _ v := v.1

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
@[simp] theorem publicSampler_cost (p : Protocol X Y R SA SB) (q : PMF p.View) :
    (publicSampler p q).cost = 0 := by
  simp [Simulator.cost, publicSampler, Protocol.cost, Tree.depth]

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem publicSampler_law (p : Protocol X Y R SA SB) (q : PMF p.View) (x : X) (y : Y) :
    ((publicSampler p q).protocol.finiteViewLaw x y).map ((publicSampler p q).aliceDecode x) = q := by
  simp only [Protocol.finiteViewLaw, PMF.map_comp]
  change ((publicSampler p q).protocol.seedLaw).map Prod.fst = q
  simp [publicSampler, Protocol.seedLaw, PMF.map_bind, PMF.pure_map, PMF.bind_pure]

omit [Fintype SA] [Fintype SB] in
@[simp] theorem publicSampler_agreement (p : Protocol X Y R SA SB) (q : PMF p.View)
    (μ : PMF (X × Y)) : (publicSampler p q).agreementError μ = 0 := by
  simp [Simulator.agreementError, publicSampler]

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]

omit [Fintype SA] [Fintype SB] in
/-- Complete zero-information case of the finite-model compression target. -/
theorem zero_information_compression (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (hinfo : externalInformation p μ = 0) :
    ∃ s : Simulator p, s.cost = 0 ∧ s.Simulates μ 0 := by
  let K : X × Y → PMF p.View := fun xy ↦ p.finiteViewLaw xy.1 xy.2
  refine ⟨publicSampler p (μ.bind K), publicSampler_cost _ _, ?_, ?_⟩
  · unfold Simulator.fidelityError
    rw [show (0 : ℝ) = ∑ xy : X × Y, (0 : ℝ) by simp]
    apply Finset.sum_le_sum
    intro xy _
    rw [publicSampler_law]
    by_cases ha : mass μ xy = 0
    · simp [ha]
    · have he := channel_constant_of_information_zero μ K hinfo xy ha
      change mass μ xy * variation (μ.bind K) (K xy) ≤ 0
      rw [he]
      simp [variation]
  · simp

end BBCR
