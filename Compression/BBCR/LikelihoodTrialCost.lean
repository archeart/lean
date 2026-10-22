module

public import BBCR.LikelihoodTrial
public import BBCR.ProtocolIteration

/-! Expected communication of the concrete trial: index messages are charged
to information; the final public-leaf proposal has constant cost. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier FiniteAzuma

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

theorem reached_nil (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (r : R) (xy : X × Y) :
    Reached p μ r xy [] := by
  constructor
  · rw [← private_prefixProbability]
    simp [StoppingFrontier.prefixProbability, map_constant, mass]
  · simp [Prefix.Prior.prefixMass, Prefix.Prior.history, Prefix.Experiment.history, mass]

omit [Fintype X] [Fintype Y] in
theorem reached_length (p : Disjointness.Protocol X Y R SA SB) (r : R) (xy : X × Y) (s : List Bool)
    (hs : 0 < Prefix.Protocol.reach p r xy.1 xy.2 s) : s.length ≤ (p.tree r).depth := by
  rw [← private_prefixProbability] at hs
  obtain ⟨ω,hω⟩ := FiniteCondition.exists_of_mass_pos (Prefix.Experiment.privateSeeds p)
    (fun ω ↦ (Prefix.Experiment.transcript p r xy.1 xy.2 ω).take s.length) s hs
  have hh := congrArg List.length hω
  have hlen := Disjointness.Tree.run_length_le_depth (p.tree r) (xy.1,ω.1) (xy.2,ω.2)
  change (Prefix.Experiment.transcript p r xy.1 xy.2 ω).length ≤ (p.tree r).depth at hlen
  simp only [List.length_take] at hh
  omega

theorem reached_endpoint (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) (w : Alphabet p μ r v xy) : Reached p μ r xy (v ++ w.1) := by
  have hh := StoppedAzuma.invariant_take (halt p μ r v xy) (Reached p μ r xy)
    (reached_child p μ ε hε hsmooth r v xy) _ v w.1 hr w.2 w.1.length le_rfl
  simpa only [List.take_length] using hh

theorem trial_expected_cost (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) :
    let d := trialData p μ r v ε (Real.exp 2) (Real.exp_pos _)
    let q := LazyIndexedRejection.protocol d (leafIndex p r v)
    expect q.seedLaw (fun seeds ↦ ((((q.tree seeds.1).run (xy.1,seeds.2.1) (xy.2,seeds.2.2)).1).length : ℝ)) ≤
      4 + 8 * Real.exp 4 * FrontierLocation.width (p.tree r).depth *
        (residual p μ r xy v - expect (target p μ r v xy) (fun w ↦ residual p μ r xy (v ++ w.1))) := by
  let d := trialData p μ r v ε (Real.exp 2) (Real.exp_pos _)
  let q := LazyIndexedRejection.protocol d (leafIndex p r v)
  let F := StoppedAzuma.finiteOutcome (p.tree r).depth (halt p μ r v xy) v
  let E := fun w : Alphabet p μ r v xy ↦ Prefix.Tree.speaker (p.tree r) (v ++ w.1) ≠ none
  let l := (FrontierLocation.width (p.tree r).depth : ℝ)
  have hpoint (seeds : Candidate p r × (IndexedRejection.Tape X (Candidate p r) (p.tree r).depth ×
      IndexedRejection.Tape Y (Candidate p r) (p.tree r).depth)) :
      ((((q.tree seeds.1).run (xy.1,seeds.2.1) (xy.2,seeds.2.2)).1).length : ℝ) =
        4 + 2 * l * (if E (F seeds.1) then 1 else 0) := by
    have hh := LazyIndexedRejection.run_length d (leafIndex p r v) seeds.1 xy.1 xy.2 seeds.2.1 seeds.2.2
    have hi := index_messages_iff p μ r v ε (Real.exp 2) (Real.exp_pos _) xy seeds.1
    change (¬(d.aliceIndex seeds.1 xy.1 = leafIndex p r v seeds.1 ∧
      d.bobIndex seeds.1 xy.2 = leafIndex p r v seeds.1)) ↔ E (F seeds.1) at hi
    by_cases he : d.aliceIndex seeds.1 xy.1 = leafIndex p r v seeds.1 ∧ d.bobIndex seeds.1 xy.2 = leafIndex p r v seeds.1
    · have hn : ¬ E (F seeds.1) := fun h ↦ hi.mpr h he
      simp only [he.1, he.2, and_self, ite_true, Nat.add_zero] at hh
      change (((LazyIndexedRejection.protocol d (leafIndex p r v)).tree seeds.1).run (xy.1,seeds.2.1) (xy.2,seeds.2.2)).1.length = 4 at hh
      rw [show ((((q.tree seeds.1).run (xy.1,seeds.2.1) (xy.2,seeds.2.2)).1).length : ℝ) = 4 by exact_mod_cast hh]
      simp [hn]
    · have hn := hi.mp he
      simp only [he, ite_false] at hh
      change (((LazyIndexedRejection.protocol d (leafIndex p r v)).tree seeds.1).run (xy.1,seeds.2.1) (xy.2,seeds.2.2)).1.length = 4 + 2 * FrontierLocation.width (p.tree r).depth at hh
      have hc : ((((q.tree seeds.1).run (xy.1,seeds.2.1) (xy.2,seeds.2.2)).1).length : ℝ) = 4 + 2 * l := by
        dsimp only [q,l]
        exact_mod_cast hh
      rw [hc]
      simp [hn]
  have hm : q.seedLaw.map Prod.fst = candidateLaw p μ r v := by
    rw [Protocol.seedLaw_eq_joint, Disjointness.FiniteLaw.joint_map_fst]
    rfl
  have he : expect q.seedLaw (fun seeds ↦ ((((q.tree seeds.1).run (xy.1,seeds.2.1) (xy.2,seeds.2.2)).1).length : ℝ)) =
      4 + 2 * l * probability (observer p μ r v xy) E := by
    unfold expect
    simp_rw [hpoint]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_mass, one_mul]
    have hsum : (∑ seeds, mass q.seedLaw seeds * (2 * l * (if E (F seeds.1) then 1 else 0))) =
        2 * l * probability q.seedLaw (fun seeds ↦ E (F seeds.1)) := by
      simp only [probability, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro seeds _
      split_ifs <;> ring
    rw [hsum]
    have hp := probability_map q.seedLaw Prod.fst (fun bits ↦ E (F bits))
    rw [hm] at hp
    rw [← hp, ← probability_map (candidateLaw p μ r v) F E, candidateLaw_frontier p μ r v xy ε]
  change expect q.seedLaw _ ≤ _
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (observer_nonterminal_le p μ ε hε hsmooth r v xy hr)
    (by positivity : 0 ≤ 2 * l)
  dsimp only [E,l]
  dsimp only [l] at hh
  nlinarith

end BBCR.LikelihoodFrontier
