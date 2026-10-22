module

public import BBCR.SmoothingTree
public import BBCR.FiniteCoupling

/-! Noisy-block smoothing as an actual private-randomness protocol. The noise
law is an explicit parameter; the iid instantiation is analyzed separately. -/

@[expose] public section

open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger
open scoped Classical

namespace BBCR.SmoothingProtocol

open SmoothingTree

variable {X Y R SA SB : Type} [Fintype R] [Fintype SA] [Fintype SB]

noncomputable def protocol (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m)) :
    Protocol X Y R (SA × Tape p.cost m) (SB × Tape p.cost m) where
  publicLaw := p.publicLaw
  aliceLaw := joint p.aliceLaw (fun _ ↦ η)
  bobLaw := joint p.bobLaw (fun _ ↦ η)
  tree r := (smooth p.cost m 0 (p.tree r)).comap
    (fun a ↦ ((a.1,a.2.1),a.2.2)) (fun b ↦ ((b.1,b.2.1),b.2.2))

theorem cost_le (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m)) :
    (protocol p m η).cost ≤ m * p.cost := by
  apply Finset.sup_le
  intro r _
  have hd := smooth_depth_le p.cost m 0 (p.tree r)
  simp only [protocol, Tree.depth_comap]
  exact hd.trans (Nat.mul_le_mul_left m (p.depth_le_cost r))

def originalSeed (p : Protocol X Y R SA SB) (m : ℕ)
    (s : R × ((SA × Tape p.cost m) × (SB × Tape p.cost m))) : R × (SA × SB) :=
  (s.1,s.2.1.1,s.2.2.1)

theorem seed_original (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m)) :
    (protocol p m η).seedLaw.map (originalSeed p m) = p.seedLaw := by
  simp only [Protocol.seedLaw, protocol, joint_eq_bind, PMF.map_bind, PMF.bind_bind,
    PMF.bind_map, PMF.map_comp, Function.comp_def, originalSeed]
  simp only [map_constant, PMF.bind_const]
  rfl

theorem seed_alice_noise (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m)) :
    (protocol p m η).seedLaw.map (fun s ↦ s.2.1.2) = η := by
  simp only [Protocol.seedLaw, protocol, joint_eq_bind, PMF.map_bind, PMF.bind_bind,
    PMF.bind_map, PMF.map_comp, Function.comp_def]
  simp only [map_constant, PMF.bind_const, PMF.bind_pure]

theorem seed_bob_noise (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m)) :
    (protocol p m η).seedLaw.map (fun s ↦ s.2.2.2) = η := by
  simp only [Protocol.seedLaw, protocol, joint_eq_bind, PMF.map_bind, PMF.bind_bind,
    PMF.bind_map, PMF.map_comp, Function.comp_def]
  simp only [PMF.bind_const]
  exact PMF.map_id _

/-- The decoder is public: it needs neither player's input or private seed. -/
def decodeView (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m))
    (v : (protocol p m η).View) : p.View :=
  ⟨v.1, ⟨decode m (p.tree v.1) v.2.1, decode_mem_leafPaths m (p.tree v.1) v.2.1⟩⟩

theorem decode_run_of_good (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m))
    (x : X) (y : Y) (s : R × ((SA × Tape p.cost m) × (SB × Tape p.cost m)))
    (ha : GoodTape s.2.1.2) (hb : GoodTape s.2.2.2) :
    decodeView p m η ((protocol p m η).runView x y s) =
      p.runView x y (originalSeed p m s) := by
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply Subtype.ext
  simpa only [decodeView, Protocol.runView, protocol, Tree.run_comap,
    originalSeed] using (SmoothingTree.decode_run_of_good p.cost m 0 (p.tree s.1)
      (x,s.2.1.1) (y,s.2.2.1) s.2.1.2 s.2.2.2 ha hb)

noncomputable def noiseError (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m)) : ℝ :=
  probability η (fun tape ↦ ¬GoodTape tape)

theorem bad_tapes_le (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m)) :
    probability (protocol p m η).seedLaw (fun s ↦ ¬GoodTape s.2.1.2 ∨ ¬GoodTape s.2.2.2) ≤
      2 * noiseError p m η := by
  refine (probability_or_le _ _ _).trans ?_
  have ha := probability_map (protocol p m η).seedLaw (fun s ↦ s.2.1.2) (fun tape ↦ ¬GoodTape tape)
  have hb := probability_map (protocol p m η).seedLaw (fun s ↦ s.2.2.2) (fun tape ↦ ¬GoodTape tape)
  rw [seed_alice_noise] at ha
  rw [seed_bob_noise] at hb
  rw [← ha, ← hb]
  exact le_of_eq (by unfold noiseError; ring)

theorem fidelity_le (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m))
    (x : X) (y : Y) :
    variation (((protocol p m η).finiteViewLaw x y).map (decodeView p m η))
      (p.finiteViewLaw x y) ≤ 2 * noiseError p m η := by
  rw [Protocol.finiteViewLaw, PMF.map_comp]
  have horiginal : p.finiteViewLaw x y =
      (protocol p m η).seedLaw.map (fun s ↦ p.runView x y (originalSeed p m s)) := by
    have hh := congrArg (fun law ↦ law.map (p.runView x y)) (seed_original p m η)
    exact (by simpa only [PMF.map_comp, Function.comp_def, Protocol.finiteViewLaw] using hh.symm)
  rw [horiginal]
  refine (variation_map_le_disagreement _ _ _).trans
    ((probability_mono _ _ _ ?_).trans (bad_tapes_le p m η))
  intro s h
  by_contra hn
  push Not at hn
  exact h (decode_run_of_good p m η x y s hn.1 hn.2)

variable [Fintype X] [Fintype Y]

noncomputable def simulator (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m)) :
    Simulator p where
  publicSeed := R
  aliceSeed := SA × Tape p.cost m
  bobSeed := SB × Tape p.cost m
  protocol := protocol p m η
  aliceDecode _ := decodeView p m η
  bobDecode _ := decodeView p m η

theorem simulates (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m))
    (μ : PMF (X × Y)) : (simulator p m η).Simulates μ (2 * noiseError p m η) := by
  constructor
  · calc
      _ ≤ ∑ xy, mass μ xy * (2 * noiseError p m η) :=
        Finset.sum_le_sum fun xy _ ↦ mul_le_mul_of_nonneg_left (fidelity_le p m η xy.1 xy.2)
          (mass_nonneg μ xy)
      _ = _ := by rw [← Finset.sum_mul, sum_mass, one_mul]
  · have hn := probability_nonneg η (fun tape ↦ ¬GoodTape tape)
    simpa [Simulator.agreementError, simulator, noiseError] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn

end BBCR.SmoothingProtocol
