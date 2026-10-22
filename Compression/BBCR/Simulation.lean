module

public import Disjointness.ChannelBridge

/-! Actual protocol simulations and the uniform BBCR compression statement. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger

namespace BBCR

variable {X Y R SA SB : Type}
  [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]

/-- A simulator contains an actual local binary protocol, followed by two local
decoders. Its target is the original full view, not merely the Boolean output. -/
structure Simulator (p : Protocol X Y R SA SB) where
  publicSeed : Type
  aliceSeed : Type
  bobSeed : Type
  [publicFinite : Fintype publicSeed]
  [aliceFinite : Fintype aliceSeed]
  [bobFinite : Fintype bobSeed]
  protocol : Protocol X Y publicSeed aliceSeed bobSeed
  aliceDecode : X → protocol.View → p.View
  bobDecode : Y → protocol.View → p.View

attribute [instance] Simulator.publicFinite Simulator.aliceFinite Simulator.bobFinite

namespace Simulator

variable {p : Protocol X Y R SA SB}

def cost (s : Simulator p) : ℕ := s.protocol.cost

noncomputable def fidelityError (s : Simulator p) (μ : PMF (X × Y)) : ℝ :=
  ∑ xy, mass μ xy * variation
    ((s.protocol.finiteViewLaw xy.1 xy.2).map (s.aliceDecode xy.1))
    (p.finiteViewLaw xy.1 xy.2)

open scoped Classical in
noncomputable def agreementError (s : Simulator p) (μ : PMF (X × Y)) : ℝ :=
  ∑ xy, mass μ xy * ∑ v, if s.aliceDecode xy.1 v = s.bobDecode xy.2 v
    then 0 else mass (s.protocol.finiteViewLaw xy.1 xy.2) v

def Simulates (s : Simulator p) (μ : PMF (X × Y)) (α : ℝ) : Prop :=
  s.fidelityError μ ≤ α ∧ s.agreementError μ ≤ α

def identity (p : Protocol X Y R SA SB) : Simulator p where
  publicSeed := R
  aliceSeed := SA
  bobSeed := SB
  protocol := p
  aliceDecode _ := id
  bobDecode _ := id

omit [Fintype X] [Fintype Y] in
@[simp] theorem identity_cost (p : Protocol X Y R SA SB) : (identity p).cost = p.cost := rfl

@[simp] theorem identity_fidelity (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    (identity p).fidelityError μ = 0 := by
  simp [fidelityError, identity, variation, PMF.map_id]

@[simp] theorem identity_agreement (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    (identity p).agreementError μ = 0 := by
  simp [agreementError, identity]

theorem identity_simulates (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    (identity p).Simulates μ 0 := by
  simp [Simulates]

end Simulator

section Information

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

/-- External information in nats. The view includes the original public seed;
private seeds remain private and are averaged out by execution. -/
noncomputable def externalInformation (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) : ℝ :=
  Disjointness.Channel.information μ (fun xy ↦ p.finiteViewLaw xy.1 xy.2)

theorem externalInformation_eq_conditional (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    externalInformation p μ = p.informationCost (joint (PMF.pure ()) (fun _ ↦ μ)) := by
  rw [Protocol.informationCost_eq_channel]
  simp [Disjointness.Channel.conditional, externalInformation, mass]

theorem externalInformation_nonneg (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    0 ≤ externalInformation p μ := by
  rw [externalInformation_eq_conditional]
  exact p.informationCost_nonneg _

theorem externalInformation_le_cost (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    externalInformation p μ ≤ (p.cost : ℝ) * Real.log 2 := by
  rw [externalInformation_eq_conditional]
  exact p.informationCost_le _

end Information

/-- Normalized form of the paper's asymptotic communication expression. The
absolute constant absorbs log-base conversion. `C+1` covers zero-bit protocols. -/
noncomputable def compressionBudget (K I : ℝ) (C : ℕ) (α : ℝ) : ℝ :=
  K * I * Real.log (((C : ℝ) + 1) / α) / α ^ 2

/-- Uniform finite-model version of BBCR 2.2, with a conditional-law simulation
guarantee. Proved by `BBCR.externalCompressionClaim` in `BBCR.Theorem22`. -/
def ExternalCompressionClaim : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (X Y R SA SB : Type)
    [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
    [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [MeasurableSpace R] [DiscreteMeasurableSpace R]
    [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
    [MeasurableSpace SB] [DiscreteMeasurableSpace SB]
    (p : Protocol X Y R SA SB) (μ : PMF (X × Y)) (α : ℝ),
    0 < α → α ≤ 1 / 2 → ∃ s : Simulator p,
      s.Simulates μ α ∧ s.cost ≤ compressionBudget K (externalInformation p μ) p.cost α

end BBCR
