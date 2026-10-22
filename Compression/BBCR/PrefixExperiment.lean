module

public import BBCR.PrefixKernels
public import BBCR.FiniteCondition

/-! Conditional next-message laws are derived from actual seed experiments.
The sender-local kernels are not independently supplied channels. -/

@[expose] public section

open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger
open scoped Classical

namespace BBCR.Prefix.Experiment

variable {X Y R SA SB : Type*} [Fintype SA] [Fintype SB]

noncomputable def privateSeeds (p : Disjointness.Protocol X Y R SA SB) : PMF (SA × SB) :=
  joint p.aliceLaw (fun _ ↦ p.bobLaw)

def transcript (p : Disjointness.Protocol X Y R SA SB) (r : R) (x : X) (y : Y)
    (ω : SA × SB) : List Bool := ((p.tree r).run (x,ω.1) (y,ω.2)).1

def history (p : Disjointness.Protocol X Y R SA SB) (r : R) (x : X) (y : Y) (k : ℕ)
    (ω : SA × SB) : List Bool := (transcript p r x y ω).take k

def message (p : Disjointness.Protocol X Y R SA SB) (r : R) (x : X) (y : Y) (k : ℕ)
    (ω : SA × SB) : Bool := (transcript p r x y ω).getD k false

theorem privateSeeds_history (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (k : ℕ) :
    (privateSeeds p).map (history p r x y k) = Protocol.law p r x y k := by
  simp only [privateSeeds, joint_eq_bind, PMF.map_bind, PMF.map_comp,
    Protocol.law, Disjointness.Protocol.privateTranscriptLaw, Function.comp_def, history, transcript]

omit [Fintype SA] [Fintype SB] in
theorem extension_event (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (bit : Bool) (ω : SA × SB) :
    history p r x y s.length ω = s ∧ message p r x y s.length ω = bit ↔
      history p r x y (s ++ [bit]).length ω = s ++ [bit] := by
  simp only [history, message, transcript]
  rw [eq_comm (a := ((p.tree r).run (x,ω.1) (y,ω.2)).1.take s.length),
    ← List.prefix_iff_eq_take,
    eq_comm (a := ((p.tree r).run (x,ω.1) (y,ω.2)).1.take (s ++ [bit]).length),
    ← List.prefix_iff_eq_take]
  exact (Tree.run_extension_iff _ _ _ _ who howner bit).symm

/-- Exact joint probability of a reached prefix and the next bit in the actual
private-seed execution. The conditional sampler is the general finite fiber law. -/
theorem conditional_message_weighted (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (bit : Bool) :
    Protocol.reach p r x y s * mass
      ((FiniteCondition.law (privateSeeds p) (history p r x y s.length) s).map
        (message p r x y s.length)) bit = Protocol.reach p r x y (s ++ [bit]) := by
  have hh := FiniteCondition.weighted_observe (privateSeeds p)
    (history p r x y s.length) (message p r x y s.length) s bit
  rw [privateSeeds_history] at hh
  change Protocol.reach p r x y s * _ = _ at hh
  rw [hh]
  unfold Protocol.reach
  rw [← privateSeeds_history, Disjointness.Channel.event_mass]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [extension_event p r x y s who howner]

/-- The normalized prefix kernel equals the actual conditional message law. -/
theorem next_eq_conditional_message (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (hpos : 0 < Protocol.reach p r x y s) :
    Protocol.next p r x y s =
      (FiniteCondition.law (privateSeeds p) (history p r x y s.length) s).map
        (message p r x y s.length) := by
  apply PMF.ext
  intro bit
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change mass (Protocol.next p r x y s) bit = _
  rw [Protocol.mass_next p r x y s who howner hpos]
  have hh := conditional_message_weighted p r x y s who howner bit
  apply (div_eq_iff hpos.ne').mpr
  exact hh.symm.trans (mul_comm _ _)

theorem aliceNext_eq_conditional_message (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool)
    (howner : Tree.speaker (p.tree r) s = some .alice) (hpos : 0 < Protocol.reach p r x y s) :
    Protocol.aliceNext p r s x =
      (FiniteCondition.law (privateSeeds p) (history p r x y s.length) s).map
        (message p r x y s.length) := by
  rw [← Protocol.next_eq_alice p r x y s howner hpos]
  exact next_eq_conditional_message p r x y s .alice howner hpos

theorem bobNext_eq_conditional_message (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool)
    (howner : Tree.speaker (p.tree r) s = some .bob) (hpos : 0 < Protocol.reach p r x y s) :
    Protocol.bobNext p r s y =
      (FiniteCondition.law (privateSeeds p) (history p r x y s.length) s).map
        (message p r x y s.length) := by
  rw [← Protocol.next_eq_bob p r x y s howner hpos]
  exact next_eq_conditional_message p r x y s .bob howner hpos

end BBCR.Prefix.Experiment
