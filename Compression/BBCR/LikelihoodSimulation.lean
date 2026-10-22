module

public import BBCR.LikelihoodLoop
public import BBCR.LikelihoodCompletion

/-! A public decoder for the bounded communication tree, and its conditional
simulation guarantee before averaging over the original public random seed. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier FiniteAzuma

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def loopDecode (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (n : ℕ)
    (v : ProtocolIteration.Plan (State p r) n (Candidate p r) × List Bool) : State p r :=
  (ProtocolIteration.decode (stepProtocol p μ ε r) (fun s ↦ terminal p r s.1) (update p r)
    n v.1 (BoundedHistory.root (p.tree r).depth) v.2).getD (BoundedHistory.root (p.tree r).depth)

theorem loopDecode_run (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (n : ℕ) (xy : X × Y) (ω) :
    loopDecode p μ ε r n (ω.1,(((loopProtocol p μ ε r n).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1) =
      loopState p μ ε r n xy ω := by
  simp only [loopDecode, loopProtocol, ProtocolIteration.protocol]
  rw [ProtocolIteration.tree_run, ProtocolIteration.decode_run]
  rfl

theorem loopState_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (n : ℕ) (xy : X × Y) :
    (loopProtocol p μ ε r n).seedLaw.map (loopState p μ ε r n xy) =
      finalLaw p μ ε r xy n (BoundedHistory.root (p.tree r).depth) := by
  unfold finalLaw
  rw [ProtocolIteration.dynamics_law]
  have hm := ProtocolIteration.regroup_law (stepProtocol p μ ε r)
    (fun s ↦ terminal p r s.1) (update p r) n (BoundedHistory.root (p.tree r).depth)
  rw [← hm, PMF.map_comp]
  congr 1
  funext ω
  exact ProtocolIteration.execute_state _ _ _ _ ω.1 ω.2.1 ω.2.2 _ _ _

theorem loop_fidelity (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε)
    (r : R) (xy : X × Y) (n : ℕ) (hn : 0 < n) :
    variation ((loopProtocol p μ ε r n).seedLaw.map (loopState p μ ε r n xy))
      (completionLaw p μ r xy (BoundedHistory.root (p.tree r).depth)) ≤
      8 * residual p μ r xy [] / (acceptanceRate * n) + Real.exp (-(acceptanceRate ^ 2 * n / 8)) := by
  have hf := final_fidelity p μ ε hε hsmooth r xy n (BoundedHistory.root (p.tree r).depth) (reached_nil p μ r xy)
  rw [← loopState_law, probability_map] at hf
  exact hf.trans (loop_unfinished p μ ε hε₀ hε hsmooth r xy n hn)

theorem boundedDecode_eq_of_length_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (n Q : ℕ) (xy : X × Y) (ω)
    (h : (((loopProtocol p μ ε r n).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1.length ≤ Q) :
    loopDecode p μ ε r n (ω.1,(((boundedLoopProtocol p μ ε r n Q).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1) =
      loopState p μ ε r n xy ω := by
  have ht : (((boundedLoopProtocol p μ ε r n Q).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1 =
      (((loopProtocol p μ ε r n).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1 := by
    rw [show (boundedLoopProtocol p μ ε r n Q).tree ω.1 =
      TreeTrace.cut Q ((loopProtocol p μ ε r n).tree ω.1) from rfl,
      TreeTrace.cut_trace, List.take_of_length_le h]
  rw [ht, loopDecode_run]

theorem bounded_state_fidelity (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε)
    (r : R) (xy : X × Y) (n Q : ℕ) (hn : 0 < n) (hQ : 4 * n < Q) :
    variation (((boundedLoopProtocol p μ ε r n Q).viewLaw xy.1 xy.2).map (loopDecode p μ ε r n))
      (completionLaw p μ r xy (BoundedHistory.root (p.tree r).depth)) ≤
      indexCoefficient p r * residual p μ r xy [] / ((Q : ℝ) - 4 * n) +
      8 * residual p μ r xy [] / (acceptanceRate * n) + Real.exp (-(acceptanceRate ^ 2 * n / 8)) := by
  let f := fun ω : LoopSeeds p r n ↦ loopDecode p μ ε r n
    (ω.1,(((boundedLoopProtocol p μ ε r n Q).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1)
  have hc := variation_map_le_disagreement (loopProtocol p μ ε r n).seedLaw f (loopState p μ ε r n xy)
  have hm : probability (loopProtocol p μ ε r n).seedLaw (fun ω ↦ f ω ≠ loopState p μ ε r n xy ω) ≤
      probability (loopProtocol p μ ε r n).seedLaw
        (fun ω ↦ Q < (((loopProtocol p μ ε r n).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1.length) := by
    apply probability_mono
    intro ω hω
    by_contra hh
    exact hω (boundedDecode_eq_of_length_le p μ ε r n Q xy ω (Nat.le_of_not_gt hh))
  have he : (((boundedLoopProtocol p μ ε r n Q).viewLaw xy.1 xy.2).map (loopDecode p μ ε r n)) =
      (loopProtocol p μ ε r n).seedLaw.map f := by
    rw [Protocol.viewLaw, PMF.map_comp]
    rfl
  rw [he]
  have ht := variation_triangle ((loopProtocol p μ ε r n).seedLaw.map f)
    ((loopProtocol p μ ε r n).seedLaw.map (loopState p μ ε r n xy))
    (completionLaw p μ r xy (BoundedHistory.root (p.tree r).depth))
  have hb := loop_cutoff p μ ε hε₀ hε hsmooth r xy n Q hQ
  have hf := loop_fidelity p μ ε hε₀ hε hsmooth r xy n hn
  linarith

end BBCR.LikelihoodFrontier
