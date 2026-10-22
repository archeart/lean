module

public import BBCR.ZeroInformation
public import BBCR.FiniteCoupling

/-! Zero-message protocols with input-dependent local decoding of public coins. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR

variable {X Y R SA SB Z : Type}
  [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB] [Fintype Z]

noncomputable def localPublicSampler (p : Protocol X Y R SA SB) (q : PMF Z)
    (a : X → Z → p.View) (b : Y → Z → p.View) : Simulator p where
  publicSeed := Z
  aliceSeed := Unit
  bobSeed := Unit
  protocol := {
    publicLaw := q
    aliceLaw := PMF.pure ()
    bobLaw := PMF.pure ()
    tree := fun _ ↦ .leaf false }
  aliceDecode x v := a x v.1
  bobDecode y v := b y v.1

omit [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB] in
@[simp] theorem localPublicSampler_cost (p : Protocol X Y R SA SB) (q : PMF Z)
    (a : X → Z → p.View) (b : Y → Z → p.View) : (localPublicSampler p q a b).cost = 0 := by
  simp [Simulator.cost,localPublicSampler,Protocol.cost,Tree.depth]

omit [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB] in
theorem localPublicSampler_law (p : Protocol X Y R SA SB) (q : PMF Z)
    (a : X → Z → p.View) (b : Y → Z → p.View) (x : X) (y : Y) :
    ((localPublicSampler p q a b).protocol.finiteViewLaw x y).map
      ((localPublicSampler p q a b).aliceDecode x) = q.map (a x) := by
  simp only [Protocol.finiteViewLaw,PMF.map_comp]
  change ((localPublicSampler p q a b).protocol.seedLaw).map (fun z ↦ a x z.1) = q.map (a x)
  simp only [localPublicSampler,Protocol.seedLaw,PMF.map_bind,PMF.pure_map,PMF.pure_bind]
  rfl

omit [Fintype R] [Fintype SA] [Fintype SB] in
theorem localPublicSampler_agreement (p : Protocol X Y R SA SB) (q : PMF Z)
    (a : X → Z → p.View) (b : Y → Z → p.View) (μ : PMF (X × Y)) :
    (localPublicSampler p q a b).agreementError μ =
      ∑ xy, mass μ xy * probability q (fun z ↦ a xy.1 z ≠ b xy.2 z) := by
  let s := localPublicSampler p q a b
  unfold Simulator.agreementError
  apply Finset.sum_congr rfl
  intro xy _
  congr 1
  have he : (∑ v, if s.aliceDecode xy.1 v = s.bobDecode xy.2 v then 0 else mass (s.protocol.finiteViewLaw xy.1 xy.2) v) =
      probability (s.protocol.finiteViewLaw xy.1 xy.2) (fun v ↦ s.aliceDecode xy.1 v ≠ s.bobDecode xy.2 v) := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : s.aliceDecode xy.1 v = s.bobDecode xy.2 v <;> simp [h]
  rw [he]
  have hf : s.protocol.finiteViewLaw xy.1 xy.2 = q.map (fun z ↦ s.protocol.runView xy.1 xy.2 (z,(),())) := by
    simp only [s,localPublicSampler,Protocol.finiteViewLaw,Protocol.seedLaw,PMF.map_bind,PMF.pure_map,PMF.pure_bind]
    rfl
  rw [hf]
  have hp := probability_map q (fun z ↦ s.protocol.runView xy.1 xy.2 (z,(),()))
    (fun v ↦ s.aliceDecode xy.1 v ≠ s.bobDecode xy.2 v)
  exact hp

end BBCR
