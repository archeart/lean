module

public import BBCR.LikelihoodDynamics

/-! Finite adaptive likelihood compression, compiled into local communication
trees, with quantitative unfinished-execution and bit-cutoff bounds. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier FiniteAzuma

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

abbrev LoopSeeds (p : Disjointness.Protocol X Y R SA SB) (r : R) (n : ℕ) :=
  ProtocolIteration.Plan (State p r) n (Candidate p r) ×
    (ProtocolIteration.Plan (State p r) n (AliceTape p r) × ProtocolIteration.Plan (State p r) n (BobTape p r))

noncomputable def loopProtocol (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (n : ℕ) : Disjointness.Protocol X Y
    (ProtocolIteration.Plan (State p r) n (Candidate p r))
    (ProtocolIteration.Plan (State p r) n (AliceTape p r))
    (ProtocolIteration.Plan (State p r) n (BobTape p r)) := ProtocolIteration.protocol (stepProtocol p μ ε r)
      (fun s ↦ terminal p r s.1) (update p r) n (BoundedHistory.root (p.tree r).depth)

noncomputable def boundedLoopProtocol (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (n Q : ℕ) : Disjointness.Protocol X Y
    (ProtocolIteration.Plan (State p r) n (Candidate p r))
    (ProtocolIteration.Plan (State p r) n (AliceTape p r))
    (ProtocolIteration.Plan (State p r) n (BobTape p r)) := ProtocolIteration.boundedProtocol (stepProtocol p μ ε r)
      (fun s ↦ terminal p r s.1) (update p r) n Q (BoundedHistory.root (p.tree r).depth)

theorem boundedLoop_cost (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (n Q : ℕ) : (boundedLoopProtocol p μ ε r n Q).cost ≤ Q :=
by
  apply Finset.sup_le
  intro rp _
  exact TreeTrace.cut_depth Q _

noncomputable def loopState (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (n : ℕ) (xy : X × Y)
    (ω : ProtocolIteration.Plan (State p r) n (Candidate p r) ×
      (ProtocolIteration.Plan (State p r) n (AliceTape p r) × ProtocolIteration.Plan (State p r) n (BobTape p r))) : State p r :=
  (ProtocolIteration.execute (stepProtocol p μ ε r) (fun s ↦ terminal p r s.1) (update p r)
    n ω.1 ω.2.1 ω.2.2 (BoundedHistory.root (p.tree r).depth) xy.1 xy.2).2

theorem loop_unfinished (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε)
    (r : R) (xy : X × Y) (n : ℕ) (hn : 0 < n) :
    probability (loopProtocol p μ ε r n).seedLaw (fun ω ↦ terminal p r (loopState p μ ε r n xy ω).1 = false) ≤
      8 * residual p μ r xy [] / (acceptanceRate * n) + Real.exp (-(acceptanceRate ^ 2 * n / 8)) := by
  have hh := completion_probability p μ ε hε₀ hε hsmooth r xy n hn
  dsimp only at hh
  rw [ProtocolIteration.dynamics_law] at hh
  have hm := ProtocolIteration.regroup_law (stepProtocol p μ ε r)
    (fun s ↦ terminal p r s.1) (update p r) n (BoundedHistory.root (p.tree r).depth)
  rw [← hm, probability_map] at hh
  have he (ω) : loopState p μ ε r n xy ω = FiniteDynamics.stateAfter (next p μ ε r xy) n
      (BoundedHistory.root (p.tree r).depth) (ProtocolIteration.regroup n ω) :=
    ProtocolIteration.execute_state _ _ _ _ ω.1 ω.2.1 ω.2.2 _ _ _
  simpa only [loopProtocol, ← he] using hh

theorem loop_bits_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (n : ℕ) (xy : X × Y) (ω) :
    ((((loopProtocol p μ ε r n).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1.length : ℝ) ≤
      4 * n + FiniteDynamics.rewardTotal (next p μ ε r xy) (indexCost p μ ε r xy) n
        (BoundedHistory.root (p.tree r).depth) (ProtocolIteration.regroup n ω) := by
  rw [show (((loopProtocol p μ ε r n).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1 =
      (ProtocolIteration.execute (stepProtocol p μ ε r) (fun s ↦ terminal p r s.1) (update p r)
        n ω.1 ω.2.1 ω.2.2 (BoundedHistory.root (p.tree r).depth) xy.1 xy.2).1 from
      ProtocolIteration.tree_run _ _ _ _ _ _ _ _ _ _, ProtocolIteration.execute_length]
  exact FiniteDynamics.rewardTotal_le _ _ _ 4 (rowCost_le p μ ε r xy) n _ _

theorem loop_cutoff (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε)
    (r : R) (xy : X × Y) (n Q : ℕ) (hQ : 4 * n < Q) :
    probability (loopProtocol p μ ε r n).seedLaw
      (fun ω ↦ Q < (((loopProtocol p μ ε r n).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1.length) ≤
      indexCoefficient p r * residual p μ r xy [] / ((Q : ℝ) - 4 * n) := by
  let g := fun ω ↦ FiniteDynamics.rewardTotal (next p μ ε r xy) (indexCost p μ ε r xy) n
    (BoundedHistory.root (p.tree r).depth) (ProtocolIteration.regroup n ω)
  have hg (ω) : 0 ≤ g ω := FiniteDynamics.reward_nonneg _ _ (indexCost_nonneg p μ ε r xy) n _ _
  have ht : 0 < (Q : ℝ) - 4 * n := by
    have hh : (4 : ℝ) * n < Q := by exact_mod_cast hQ
    linarith
  have hm := probability_le_expect_div (loopProtocol p μ ε r n).seedLaw g ((Q : ℝ) - 4 * n) ht (fun ω _ ↦ hg ω)
  have he := expected_index_total p μ ε hε₀ hε hsmooth r xy n
  dsimp only at he
  rw [ProtocolIteration.dynamics_law] at he
  have hl := ProtocolIteration.regroup_law (stepProtocol p μ ε r)
    (fun s ↦ terminal p r s.1) (update p r) n (BoundedHistory.root (p.tree r).depth)
  rw [← hl, expect_map] at he
  apply (le_trans (probability_mono _ _ _ ?_) hm).trans
  · exact div_le_div_of_nonneg_right he ht.le
  · intro ω hω
    have hb := loop_bits_le p μ ε r n xy ω
    have hw : (Q : ℝ) < (((loopProtocol p μ ε r n).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1.length := by exact_mod_cast hω
    dsimp only [g]
    linarith

end BBCR.LikelihoodFrontier
