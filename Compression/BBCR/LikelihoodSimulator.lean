module

public import BBCR.LikelihoodSimulation
public import BBCR.ProtocolFamily

/-! A simulator of the original finite view, with shared public decoding and
independent private seeds, obtained by mixing the concrete bounded loops. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.TreeTrace

variable {A B : Type*}

def firstLeaf : Tree A B → List Bool
  | .leaf _ => []
  | .alice _ z _ => false :: firstLeaf z
  | .bob _ z _ => false :: firstLeaf z

theorem firstLeaf_mem (t : Tree A B) : firstLeaf t ∈ t.leafPaths := by
  induction t with
  | leaf o => simp [firstLeaf,Tree.leafPaths]
  | alice q z o hz ho => simp only [firstLeaf,Tree.leafPaths]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,hz,rfl⟩)
  | bob q z o hz ho => simp only [firstLeaf,Tree.leafPaths]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,hz,rfl⟩)

end BBCR.TreeTrace

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier FiniteAzuma

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def stateView (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : State p r) : p.View :=
  ⟨r,if h : s.1 ∈ (p.tree r).leafPaths then ⟨s.1,h⟩ else ⟨TreeTrace.firstLeaf (p.tree r),TreeTrace.firstLeaf_mem _⟩⟩

noncomputable def conditionalViewLaw (p : Disjointness.Protocol X Y R SA SB) (r : R) (xy : X × Y) : PMF p.View :=
  (Prefix.Experiment.privateSeeds p).map (fun ω ↦ p.runView xy.1 xy.2 (r,ω))

theorem root_completion_view (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (r : R) (xy : X × Y) :
    (completionLaw p μ r xy (BoundedHistory.root (p.tree r).depth)).map (stateView p r) = conditionalViewLaw p r xy := by
  unfold completionLaw
  dsimp only [BoundedHistory.root]
  rw [leaf_law p μ r xy, PMF.map_comp, PMF.map_comp]
  congr 1
  funext ω
  have hl := Tree.run_length_le_depth (p.tree r) (xy.1,ω.1) (xy.2,ω.2)
  have hm := Tree.run_mem_leafPaths (p.tree r) (xy.1,ω.1) (xy.2,ω.2)
  change stateView p r (advance p r (BoundedHistory.root (p.tree r).depth)
    (((p.tree r).run (xy.1,ω.1) (xy.2,ω.2)).1)) = p.runView xy.1 xy.2 (r,ω)
  have ha : advance p r (BoundedHistory.root (p.tree r).depth)
      (((p.tree r).run (xy.1,ω.1) (xy.2,ω.2)).1) =
      ⟨((p.tree r).run (xy.1,ω.1) (xy.2,ω.2)).1,hl⟩ := by
    have hfull : ((BoundedHistory.root (p.tree r).depth).1 ++
        ((p.tree r).run (xy.1,ω.1) (xy.2,ω.2)).1).length ≤ (p.tree r).depth := hl
    unfold advance
    rw [dite_eq_left hfull]
    rfl
  rw [ha]
  simp only [stateView, hm, dite_true, Protocol.runView]
  rfl

omit [Fintype X] [Fintype Y] in
theorem conditionalViewLaw_average (p : Disjointness.Protocol X Y R SA SB) (xy : X × Y) :
    p.publicLaw.bind (fun r ↦ conditionalViewLaw p r xy) = p.finiteViewLaw xy.1 xy.2 := by
  simp only [conditionalViewLaw, Prefix.Experiment.privateSeeds, Disjointness.FiniteLaw.joint_eq_bind,
    Protocol.finiteViewLaw, Protocol.seedLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]

variable [Fintype R]

noncomputable def simulator (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (n Q : ℕ) : Simulator p where
  publicSeed := Σ r, ProtocolIteration.Plan (State p r) n (Candidate p r)
  aliceSeed := (r : R) → ProtocolIteration.Plan (State p r) n (AliceTape p r)
  bobSeed := (r : R) → ProtocolIteration.Plan (State p r) n (BobTape p r)
  protocol := ProtocolFamily.protocol p.publicLaw (fun r ↦ boundedLoopProtocol p μ ε r n Q)
  aliceDecode _ v := stateView p v.1.1 (loopDecode p μ ε v.1.1 n (v.1.2,v.2.1))
  bobDecode _ v := stateView p v.1.1 (loopDecode p μ ε v.1.1 n (v.1.2,v.2.1))

theorem simulator_cost (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (ε : ℝ) (n Q : ℕ) :
    (simulator p μ ε n Q).cost ≤ Q := by
  exact ProtocolFamily.cost_le _ _ Q (fun r ↦ boundedLoop_cost p μ ε r n Q)

theorem simulator_agreement (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (ε : ℝ) (n Q : ℕ) :
    (simulator p μ ε n Q).agreementError μ = 0 := by
  simp [Simulator.agreementError,simulator]

theorem simulator_decoded_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (n Q : ℕ) (xy : X × Y) :
    ((simulator p μ ε n Q).protocol.finiteViewLaw xy.1 xy.2).map ((simulator p μ ε n Q).aliceDecode xy.1) =
      p.publicLaw.bind (fun r ↦ (((boundedLoopProtocol p μ ε r n Q).viewLaw xy.1 xy.2).map
        (loopDecode p μ ε r n)).map (stateView p r)) := by
  have hh := ProtocolFamily.decoded_law p.publicLaw (fun r ↦ boundedLoopProtocol p μ ε r n Q)
    (fun r v ↦ stateView p r (loopDecode p μ ε r n v)) xy.1 xy.2
  have he : ((simulator p μ ε n Q).protocol.finiteViewLaw xy.1 xy.2).map ((simulator p μ ε n Q).aliceDecode xy.1) =
      ((simulator p μ ε n Q).protocol.viewLaw xy.1 xy.2).map
        (fun v ↦ stateView p v.1.1 (loopDecode p μ ε v.1.1 n (v.1.2,v.2))) := by
    rw [← Protocol.finiteViewLaw_map, PMF.map_comp]
    rfl
  rw [he]
  simpa only [simulator, PMF.map_comp, Function.comp_def] using hh

theorem simulator_pointwise_fidelity (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε)
    (n Q : ℕ) (hn : 0 < n) (hQ : 4 * n < Q) (xy : X × Y) :
    variation (((simulator p μ ε n Q).protocol.finiteViewLaw xy.1 xy.2).map ((simulator p μ ε n Q).aliceDecode xy.1))
      (p.finiteViewLaw xy.1 xy.2) ≤
      ∑ r, mass p.publicLaw r * (indexCoefficient p r * residual p μ r xy [] / ((Q : ℝ) - 4 * n) +
        8 * residual p μ r xy [] / (acceptanceRate * n) + Real.exp (-(acceptanceRate ^ 2 * n / 8))) := by
  rw [simulator_decoded_law, ← conditionalViewLaw_average]
  apply (variation_bind_le _ _ _).trans
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ (mass_nonneg _ _)
  rw [← root_completion_view p μ r xy]
  exact (variation_map_le _ _ (stateView p r)).trans (bounded_state_fidelity p μ ε hε₀ hε hsmooth r xy n Q hn hQ)

end BBCR.LikelihoodFrontier
