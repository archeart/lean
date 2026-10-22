module

public import BBCR.NoiseNextBit
public import BBCR.FreshCoin

/-! The noisy-block construction is an actual beta-smooth private-randomness
protocol. Conditional probabilities are bounded only at reached internal nodes;
null histories and already terminated executions transmit no further bit. -/

@[expose] public section

open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger
open scoped Classical

namespace BBCR

variable {X Y R SA SB : Type} [Fintype SA] [Fintype SB]

def Smooth (p : Protocol X Y R SA SB) (β : ℝ) : Prop :=
  ∀ (r : R) (x : X) (y : Y) (s : List Bool) (who : Prefix.Speaker),
    Prefix.Tree.speaker (p.tree r) s = some who →
    0 < Prefix.Protocol.reach p r x y s →
    mass (Prefix.Protocol.next p r x y s) true ∈ Set.Icc (1 / 2 - β) (1 / 2 + β)

namespace SmoothingProtocol

open SmoothingTree

variable [Fintype R]

def resampleSeed (p : Protocol X Y R SA SB) (m : ℕ) (who : Prefix.Speaker)
    (i : Fin (p.cost + 1)) (j : Fin m)
    (ω : (SA × Tape p.cost m) × (SB × Tape p.cost m)) (bit : Bool) :
    (SA × Tape p.cost m) × (SB × Tape p.cost m) :=
  ((ω.1.1,modifyTape who .alice ω.1.2 i j bit),
    (ω.2.1,modifyTape who .bob ω.2.2 i j bit))

theorem private_resample (p : Protocol X Y R SA SB) (m : ℕ)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) (who : Prefix.Speaker)
    (i : Fin (p.cost + 1)) (j : Fin m) :
    let η := SmoothingCoupling.tapeLaw p.cost m β hβ₀ hβ₁
    (joint (SmoothingNoise.coin β hβ₀ hβ₁)
      (fun _ ↦ Prefix.Experiment.privateSeeds (protocol p m η))).map
        (fun z ↦ resampleSeed p m who i j z.2 z.1) =
      Prefix.Experiment.privateSeeds (protocol p m η) := by
  let η := SmoothingCoupling.tapeLaw p.cost m β hβ₀ hβ₁
  let c := SmoothingNoise.coin β hβ₀ hβ₁
  have ht := SmoothingCoupling.tapeLaw_resample p.cost m β hβ₀ hβ₁ i j
  cases who with
  | alice =>
    have ha := joint_resample_right p.aliceLaw η c (fun tape bit ↦ updateBit tape i j bit) ht
    have h := joint_resample_left (joint p.aliceLaw (fun _ ↦ η))
      (joint p.bobLaw (fun _ ↦ η)) c (fun z bit ↦ (z.1,updateBit z.2 i j bit)) ha
    simpa [resampleSeed, modifyTape, Prefix.Experiment.privateSeeds, protocol] using h
  | bob =>
    have hb := joint_resample_right p.bobLaw η c (fun tape bit ↦ updateBit tape i j bit) ht
    have h := joint_resample_right (joint p.aliceLaw (fun _ ↦ η))
      (joint p.bobLaw (fun _ ↦ η)) c (fun z bit ↦ (z.1,updateBit z.2 i j bit)) hb
    simpa [resampleSeed, modifyTape, Prefix.Experiment.privateSeeds, protocol] using h

theorem transcript_eq (p : Protocol X Y R SA SB) (m : ℕ) (η : PMF (Tape p.cost m))
    (r : R) (x : X) (y : Y) (ω : (SA × Tape p.cost m) × (SB × Tape p.cost m)) :
    Prefix.Experiment.transcript (protocol p m η) r x y ω =
      ((smooth p.cost m 0 (p.tree r)).run ((x,ω.1.1),ω.1.2) ((y,ω.2.1),ω.2.2)).1 := by
  simp only [Prefix.Experiment.transcript, protocol, Disjointness.Tree.run_comap]

/-- Definition 8.3 for the actual smoothing construction. The proof derives
freshness from the private product seed law and pointwise prefix causality. -/
theorem smooth (p : Protocol X Y R SA SB) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    Smooth (protocol p m (SmoothingCoupling.tapeLaw p.cost m β hβ₀ hβ₁)) β := by
  intro r x y s who howner hpos
  let η := SmoothingCoupling.tapeLaw p.cost m β hβ₀ hβ₁
  let q := protocol p m η
  let H := Prefix.Experiment.history q r x y s.length
  let G := Prefix.Experiment.message q r x y s.length
  have hH : 0 < mass ((Prefix.Experiment.privateSeeds q).map H) s := by
    rw [Prefix.Experiment.privateSeeds_history]
    exact hpos
  obtain ⟨ω,hω⟩ := FiniteCondition.exists_of_mass_pos (Prefix.Experiment.privateSeeds q) H s hH
  have hact : Prefix.Tree.speaker (q.tree r)
      (((q.tree r).run (x,ω.1) (y,ω.2)).1.take s.length) ≠ none := by
    change Prefix.Tree.speaker (q.tree r) (H ω) ≠ none
    rw [hω, howner]
    exact Option.some_ne_none _
  have hlen : s.length < ((q.tree r).run (x,ω.1) (y,ω.2)).1.length :=
    Nat.lt_of_not_ge (fun hh ↦ hact ((Prefix.Tree.speaker_take_eq_none_iff _ _ _ _).mpr hh))
  have hbudget : (q.tree r).depth ≤ m * p.cost :=
    (q.depth_le_cost r).trans (cost_le p m η)
  have htotal : s.length < m * p.cost :=
    hlen.trans_le ((Disjointness.Tree.run_length_le_depth _ _ _).trans hbudget)
  have hd : s.length / m < p.cost :=
    (Nat.div_lt_iff_lt_mul hm).mpr (by simpa only [Nat.mul_comm] using htotal)
  let j : Fin m := ⟨s.length % m, Nat.mod_lt _ hm⟩
  have hk : s.length = (s.length / m) * m + j.val := by
    dsimp only [j]
    simpa only [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div s.length m).symm
  let i := tapeIndex p.cost (s.length / m)
  let u := resampleSeed p m who i j
  have hstable : ∀ ω bit, H (u ω bit) = H ω := by
    intro ω bit
    have hc := fresh_prefix p.cost m (p.tree r) 0 (s.length / m) (by omega) j who
      (x,ω.1.1) (y,ω.2.1) ω.1.2 ω.2.2 bit
    dsimp only [H, Prefix.Experiment.history, q]
    rw [transcript_eq, transcript_eq]
    simpa only [u, resampleSeed, i, Nat.zero_add, ← hk] using hc
  have hflip : ∀ ω, H ω = s → G (u ω false) = !(G (u ω true)) := by
    intro ω hh
    have hphysical :
        (((SmoothingTree.smooth p.cost m 0 (p.tree r)).run
          ((x,ω.1.1),ω.1.2) ((y,ω.2.1),ω.2.2)).1).take s.length = s := by
      simpa only [H, Prefix.Experiment.history, q, transcript_eq] using hh
    have howner' : Prefix.Tree.speaker (SmoothingTree.smooth p.cost m 0 (p.tree r)) s = some who := by
      simpa only [protocol, Prefix.Tree.speaker_comap] using howner
    have hp : Prefix.Tree.speaker (SmoothingTree.smooth p.cost m 0 (p.tree r))
        ((((SmoothingTree.smooth p.cost m 0 (p.tree r)).run
          ((x,ω.1.1),ω.1.2) ((y,ω.2.1),ω.2.2)).1).take ((s.length / m) * m + j.val)) = some who := by
      rw [← hk, hphysical]
      exact howner'
    have hc := fresh_message_complement p.cost m (p.tree r) 0 (s.length / m) (by omega) j who
      (x,ω.1.1) (y,ω.2.1) ω.1.2 ω.2.2 hp
    dsimp only [G, Prefix.Experiment.message, q]
    rw [transcript_eq, transcript_eq]
    simpa only [u, resampleSeed, i, Nat.zero_add, ← hk] using hc
  rw [Prefix.Experiment.next_eq_conditional_message q r x y s who howner hpos]
  exact fresh_coin_conditional (Prefix.Experiment.privateSeeds q) β hβ₀ hβ₁ u
    (private_resample p m β hβ₀ hβ₁ who i j) H G s hH hstable hflip

variable [Fintype X] [Fintype Y]

/-- Communication, fidelity, and beta-smoothness hold for the same concrete
simulator. The comparison of divergence to the original information is separate. -/
theorem smooth_simulation (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (hm : 0 < m) (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    let s := simulator p m (SmoothingCoupling.tapeLaw p.cost m β hβ₀ hβ₁)
    Smooth s.protocol β ∧ s.cost ≤ m * p.cost ∧
      s.Simulates μ (2 * ((p.cost : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2)) :=
  ⟨smooth p m hm β hβ₀ hβ₁, SmoothingCoupling.smoothing_simulation p μ m hm β hβ₀ hβ₁⟩

end SmoothingProtocol
end BBCR
