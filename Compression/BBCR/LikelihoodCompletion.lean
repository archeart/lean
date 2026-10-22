module

public import BBCR.LikelihoodDynamics
public import BBCR.KernelCompletion
public import BBCR.KernelCoupling

/-! Exact frontier trials preserve every terminal payoff. This identifies the
output distribution, in addition to the loop's progress and communication. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier FiniteAzuma

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def payoff (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (f : List Bool → ℝ) (s : State p r) : ℝ :=
  KernelCompletion.value (p.tree r).depth (terminal p r) (targetKernel p μ r xy) f s.1

theorem payoff_step (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (f : List Bool → ℝ) (s : State p r) (hs : Reached p μ r xy s.1) :
    expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r))
      (fun row ↦ payoff p μ r xy f (next p μ ε r xy s row)) = payoff p μ r xy f s := by
  cases ht : terminal p r s.1 with
  | true => simp [next, ProtocolIteration.rowNext, ht, expect_const]
  | false =>
    rw [expect_next p μ ε hε hsmooth r xy s hs ht]
    have he : (fun w : Alphabet p μ r s.1 xy ↦ payoff p μ r xy f (advance p r s w.1)) =
        fun w ↦ KernelCompletion.value (p.tree r).depth (terminal p r) (targetKernel p μ r xy) f (s.1 ++ w.1) := by
      funext w
      exact congrArg (KernelCompletion.value _ _ _ f) (advance_frontier p μ ε hε hsmooth r s xy hs w).1
    rw [he]
    have hh := KernelCompletion.frontier_harmonic (p.tree r).depth (terminal p r)
      (halt p μ r s.1 xy) (targetKernel p μ r xy) f (terminal_implies_halt p μ r s.1 xy)
      (terminal_depth p r) (p.tree r).depth s.1
    change expect (target p μ r s.1 xy) _ = payoff p μ r xy f s at hh
    rw [hh]
    ring

theorem payoff_invariant (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (f : List Bool → ℝ) (n : ℕ) (s : State p r) (hs : Reached p μ r xy s.1) :
    expect (FiniteDynamics.process (ProtocolIteration.rowLaw (stepProtocol p μ ε r))
      (next p μ ε r xy) (fun _ _ ↦ 0) n s).law
      (fun bits ↦ payoff p μ r xy f (FiniteDynamics.stateAfter (next p μ ε r xy) n s bits)) = payoff p μ r xy f s :=
  FiniteDynamics.expect_final _ _ _ _ (fun t ↦ Reached p μ r xy t.1)
    (next_invariant p μ ε hε hsmooth r xy) (payoff_step p μ ε hε hsmooth r xy f) n s hs

theorem public_reached_child (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : List Bool) (hs : Reached p μ r xy s) (ht : terminal p r s = false) (b : Bool) :
    Reached p μ r xy (s ++ [b]) := by
  apply reached_child p μ ε hε hsmooth r s xy s hs _ b
  have hn : Prefix.Tree.speaker (p.tree r) s ≠ none := by simpa [terminal] using ht
  simp [halt, localSum, StoppedAzuma.incrementSum, hn]

theorem full_endpoint (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : State p r) (hs : Reached p μ r xy s.1)
    (w : ↥(StoppingFrontier.paths (p.tree r).depth (terminal p r) s.1)) :
    (advance p r s w.1).1 = s.1 ++ w.1 ∧ terminal p r (s.1 ++ w.1) = true := by
  have hh := StoppedAzuma.invariant_take (terminal p r) (Reached p μ r xy)
    (public_reached_child p μ ε hε hsmooth r xy) _ s.1 w.1 hs w.2 w.1.length le_rfl
  simp only [List.take_length] at hh
  have hl := reached_length p r xy _ hh.1
  have ht : terminal p r (s.1 ++ w.1) = true := by
    rcases StoppingFrontier.halt_or_length_eq _ (terminal p r) s.1 w.1 w.2 with ht | he
    · exact ht
    · exact terminal_depth p r _ (by simp [he])
  simp only [advance, hl, dite_true]
  exact ⟨trivial,ht⟩

noncomputable def completionLaw (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : State p r) : PMF (State p r) :=
  (StoppingFrontier.finiteLaw (p.tree r).depth (terminal p r) (targetKernel p μ r xy) s.1).map
    (fun w ↦ advance p r s w.1)

theorem completionLaw_terminal (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : State p r) (hs : terminal p r s.1 = true) :
    completionLaw p μ r xy s = PMF.pure s := by
  unfold completionLaw
  rw [← StoppedAzuma.process_finiteLaw _ _ (fun _ _ ↦ 0) (fun _ ↦ 0), PMF.map_comp]
  have he : (fun bits ↦ advance p r s (StoppedAzuma.finiteOutcome (p.tree r).depth (terminal p r) s.1 bits).1) =
      fun _ ↦ s := by
    funext bits
    have hz (n : ℕ) (bits : Fin n → Bool) : StoppedAzuma.outcome n (terminal p r) s.1 bits = [] := by
      cases n <;> simp [StoppedAzuma.outcome, hs]
    simp only [StoppedAzuma.finiteOutcome, hz, advance, List.append_nil,
      s.2, dite_true]
  change PMF.map (fun bits ↦ advance p r s (StoppedAzuma.finiteOutcome _ _ _ bits).1) _ = _
  rw [he, map_constant]

theorem completionLaw_mass (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : State p r) (hs : Reached p μ r xy s.1) (a : State p r) :
    mass (completionLaw p μ r xy s) a = payoff p μ r xy (fun t ↦ if t = a.1 then 1 else 0) s := by
  have hh := KernelCompletion.frontier_harmonic (p.tree r).depth (terminal p r)
    (terminal p r) (targetKernel p μ r xy) (fun t ↦ if t = a.1 then 1 else 0)
    (fun _ ht ↦ ht) (terminal_depth p r) (p.tree r).depth s.1
  have he (w : ↥(StoppingFrontier.paths (p.tree r).depth (terminal p r) s.1)) :
      KernelCompletion.value (p.tree r).depth (terminal p r) (targetKernel p μ r xy)
        (fun t ↦ if t = a.1 then (1 : ℝ) else 0) (s.1 ++ w.1) =
        if advance p r s w.1 = a then 1 else 0 := by
    obtain ⟨ha,ht⟩ := full_endpoint p μ ε hε hsmooth r xy s hs w
    rw [KernelCompletion.value_terminal _ _ _ _ _ ht, ← ha]
    simp only [Subtype.val_inj]
  simp_rw [he] at hh
  change _ = payoff p μ r xy _ s at hh
  rw [← hh]
  unfold completionLaw
  rw [mass_map_sum]
  unfold expect
  apply Finset.sum_congr rfl
  intro w _
  dsimp only
  split_ifs <;> ring

noncomputable def finalLaw (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (xy : X × Y) (n : ℕ) (s : State p r) : PMF (State p r) :=
  (FiniteDynamics.process (ProtocolIteration.rowLaw (stepProtocol p μ ε r))
    (next p μ ε r xy) (fun _ _ ↦ 0) n s).law.map (FiniteDynamics.stateAfter (next p μ ε r xy) n s)

theorem final_completion_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (n : ℕ) (s : State p r) (hs : Reached p μ r xy s.1) :
    (finalLaw p μ ε r xy n s).bind (completionLaw p μ r xy) = completionLaw p μ r xy s := by
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change mass _ a = mass _ a
  rw [Disjointness.Channel.mass_bind]
  change expect (finalLaw p μ ε r xy n s) (fun t ↦ mass (completionLaw p μ r xy t) a) = _
  rw [finalLaw, expect_map]
  have he (bits) : mass (completionLaw p μ r xy (FiniteDynamics.stateAfter (next p μ ε r xy) n s bits)) a =
      payoff p μ r xy (fun t ↦ if t = a.1 then 1 else 0) (FiniteDynamics.stateAfter (next p μ ε r xy) n s bits) :=
    completionLaw_mass p μ ε hε hsmooth r xy _
      (FiniteDynamics.state_invariant _ _ (next_invariant p μ ε hε hsmooth r xy) n s hs bits) a
  simp_rw [he]
  rw [payoff_invariant p μ ε hε hsmooth r xy _ n s hs, completionLaw_mass p μ ε hε hsmooth r xy s hs a]

theorem final_fidelity (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (n : ℕ) (s : State p r) (hs : Reached p μ r xy s.1) :
    variation (finalLaw p μ ε r xy n s) (completionLaw p μ r xy s) ≤
      probability (finalLaw p μ ε r xy n s) (fun t ↦ terminal p r t.1 = false) := by
  have hh := variation_completion_le (finalLaw p μ ε r xy n s) (completionLaw p μ r xy) id
    (fun t ↦ terminal p r t.1 = true) (completionLaw_terminal p μ r xy)
  rw [PMF.map_id, final_completion_law p μ ε hε hsmooth r xy n s hs] at hh
  apply hh.trans_eq
  unfold probability
  apply Finset.sum_congr rfl
  intro t _
  cases terminal p r t.1 <;> simp

end BBCR.LikelihoodFrontier
