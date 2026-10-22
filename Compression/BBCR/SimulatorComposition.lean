module

public import BBCR.KernelCoupling

/-! Composition through a common public decoder preserves communication and
adds fidelity errors. Local agreement is inherited from the inner simulator. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.Simulator

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
variable {p : Protocol X Y R SA SB}

set_option maxHeartbeats 1000000

noncomputable def composePublic (s : Simulator p) (t : Simulator s.protocol)
    (decode : s.protocol.View → p.View) : Simulator p where
  publicSeed := t.publicSeed
  aliceSeed := t.aliceSeed
  bobSeed := t.bobSeed
  protocol := t.protocol
  aliceDecode x v := decode (t.aliceDecode x v)
  bobDecode y v := decode (t.bobDecode y v)

omit [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB] in
theorem composePublic_cost (s : Simulator p) (t : Simulator s.protocol) (decode : s.protocol.View → p.View) :
    (composePublic s t decode).cost = t.cost := rfl

omit [Fintype SA] [Fintype SB] in
theorem composePublic_fidelity (s : Simulator p) (t : Simulator s.protocol) (decode : s.protocol.View → p.View)
    (hdecode : ∀ x, s.aliceDecode x = decode) (μ : PMF (X × Y)) :
    (composePublic s t decode).fidelityError μ ≤ t.fidelityError μ + s.fidelityError μ := by
  unfold fidelityError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro xy _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (mass_nonneg μ xy)
  have hh := (variation_triangle (((t.protocol.finiteViewLaw xy.1 xy.2).map (t.aliceDecode xy.1)).map decode)
    ((s.protocol.finiteViewLaw xy.1 xy.2).map decode) (p.finiteViewLaw xy.1 xy.2)).trans
      (add_le_add (variation_map_le ((t.protocol.finiteViewLaw xy.1 xy.2).map (t.aliceDecode xy.1))
        (s.protocol.finiteViewLaw xy.1 xy.2) decode) le_rfl)
  simpa only [composePublic, PMF.map_comp, Function.comp_def, hdecode xy.1] using hh

omit [Fintype R] [Fintype SA] [Fintype SB] in
theorem composePublic_agreement (s : Simulator p) (t : Simulator s.protocol) (decode : s.protocol.View → p.View)
    (μ : PMF (X × Y)) : (composePublic s t decode).agreementError μ ≤ t.agreementError μ := by
  unfold agreementError
  apply Finset.sum_le_sum
  intro xy _
  apply mul_le_mul_of_nonneg_left _ (mass_nonneg μ xy)
  apply Finset.sum_le_sum
  intro v _
  change (if decode (t.aliceDecode xy.1 v) = decode (t.bobDecode xy.2 v) then 0 else _) ≤ _
  by_cases h : t.aliceDecode xy.1 v = t.bobDecode xy.2 v
  · simp [h]
  · simp only [h, ite_false]
    split_ifs
    · exact mass_nonneg _ _
    · rfl

omit [Fintype SA] [Fintype SB] in
theorem composePublic_simulates (s : Simulator p) (t : Simulator s.protocol) (decode : s.protocol.View → p.View)
    (hdecode : ∀ x, s.aliceDecode x = decode) (μ : PMF (X × Y)) (α β : ℝ)
    (hα : 0 ≤ α) (hs : s.Simulates μ α) (ht : t.Simulates μ β) :
    (composePublic s t decode).Simulates μ (α + β) := by
  constructor
  · have hh := (composePublic_fidelity s t decode hdecode μ).trans (add_le_add ht.1 hs.1)
    simpa only [add_comm] using hh
  · exact (composePublic_agreement s t decode μ).trans (ht.2.trans (le_add_of_nonneg_left hα))

end BBCR.Simulator
