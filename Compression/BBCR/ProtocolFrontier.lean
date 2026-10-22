module

public import BBCR.StoppedExecution
public import BBCR.PrefixAccounting

/-! BBCR's input-dependent divergence frontier and its four probability laws.
Their factorization is derived from actual sender-local protocol kernels. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.ProtocolFrontier

open Prefix

variable {X Y R SA SB : Type*} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def accumulated (d : List Bool → ℝ) (start : ℕ) (s : List Bool) : ℝ :=
  ∑ j ∈ Finset.Ico start s.length, d (s.take j)

/-- Stop at the first leaf or when either player's accumulated local KL reaches
the threshold. The starting prefix contributes no divergence to this round. -/
noncomputable def halt (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (s : List Bool) : Bool :=
  decide (Tree.speaker (p.tree r) s = none ∨ β ≤ max
    (accumulated (fun t ↦ Prior.aliceDivergence p μ r t xy) v.length s)
    (accumulated (fun t ↦ Prior.bobDivergence p μ r t xy) v.length s))

theorem halt_start (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (hβ : 0 < β) (who : Speaker)
    (hv : Tree.speaker (p.tree r) v = some who) : halt p μ r v xy β v = false := by
  simp [halt, accumulated, hv, not_le_of_gt hβ]

/-- Both local divergence budgets are strictly below the threshold at every
strict ancestor of a frontier atom, as required by the paper's definition. -/
theorem accumulated_lt_before_frontier (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (w : List Bool)
    (hw : w ∈ StoppingFrontier.paths (p.tree r).depth (halt p μ r v xy β) v)
    (j : ℕ) (hj : j < w.length) :
    let s := v ++ w.take j
    accumulated (fun t ↦ Prior.aliceDivergence p μ r t xy) v.length s < β ∧
      accumulated (fun t ↦ Prior.bobDivergence p μ r t xy) v.length s < β := by
  have hs := StoppingFrontier.not_halt_take (p.tree r).depth (halt p μ r v xy β) v w hw j hj
  simp only [halt, decide_eq_false_iff_not, not_or, not_le] at hs
  exact ⟨(le_max_left _ _).trans_lt hs.2,(le_max_right _ _).trans_lt hs.2⟩

/-- On actual complete executions, finite recursion stops at a leaf or a
threshold crossing, never merely because the recursion fuel ran out. -/
theorem hit_terminal_condition (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (x : X) (y : Y) (ω : SA × SB)
    (hv : v.IsPrefix (Experiment.transcript p r x y ω)) :
    let w := StoppingFrontier.hit (p.tree r).depth (halt p μ r v xy β) v
      ((Experiment.transcript p r x y ω).drop v.length)
    halt p μ r v xy β (v ++ w) = true := by
  apply StoppingFrontier.halt_hit
  · simp only [List.length_drop]
    have hh := Disjointness.Tree.run_length_le_depth (p.tree r) (x,ω.1) (y,ω.2)
    change (Experiment.transcript p r x y ω).length ≤ (p.tree r).depth at hh
    omega
  · rw [← List.prefix_append_drop hv]
    have hh := (Tree.speaker_take_eq_none_iff (p.tree r) (x,ω.1) (y,ω.2)
      ((p.tree r).run (x,ω.1) (y,ω.2)).1.length).mpr le_rfl
    simp only [List.take_length] at hh
    simp [halt, Experiment.transcript, hh]

noncomputable def aliceKernel (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (x : X) (s : List Bool) : PMF Bool :=
  if Tree.speaker (p.tree r) s = some .alice then Protocol.aliceNext p r s x
    else Prior.observerNext p μ r s

noncomputable def bobKernel (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (y : Y) (s : List Bool) : PMF Bool :=
  if Tree.speaker (p.tree r) s = some .bob then Protocol.bobNext p r s y
    else Prior.observerNext p μ r s

noncomputable def targetKernel (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : List Bool) : PMF Bool :=
  match Tree.speaker (p.tree r) s with
  | some .alice => Protocol.aliceNext p r s xy.1
  | some .bob => Protocol.bobNext p r s xy.2
  | none => Prior.observerNext p μ r s

theorem kernel_factorization (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : List Bool) (b : Bool) :
    mass (aliceKernel p μ r xy.1 s) b * mass (bobKernel p μ r xy.2 s) b =
      mass (Prior.observerNext p μ r s) b * mass (targetKernel p μ r xy s) b := by
  cases h : Tree.speaker (p.tree r) s with
  | none => simp [aliceKernel, bobKernel, targetKernel, h]
  | some who => cases who <;> simp [aliceKernel, bobKernel, targetKernel, h, mul_comm]

theorem weighted_targetKernel (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (b : Bool) :
    Protocol.reach p r xy.1 xy.2 s * mass (targetKernel p μ r xy s) b =
      Protocol.reach p r xy.1 xy.2 (s ++ [b]) := by
  calc
    _ = Protocol.reach p r xy.1 xy.2 s * mass (Protocol.next p r xy.1 xy.2 s) b := by
      by_cases hp : 0 < Protocol.reach p r xy.1 xy.2 s
      · cases who with
        | alice => rw [targetKernel, howner, Protocol.next_eq_alice p r xy.1 xy.2 s howner hp]
        | bob => rw [targetKernel, howner, Protocol.next_eq_bob p r xy.1 xy.2 s howner hp]
      · have hz := le_antisymm (le_of_not_gt hp) (Protocol.reach_nonneg p r xy.1 xy.2 s)
        rw [hz, zero_mul, zero_mul]
    _ = _ := Protocol.weighted_mass_next p r xy.1 xy.2 s who howner b

theorem weighted_observerKernel (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (b : Bool) :
    Prior.prefixMass p μ r s * mass (Prior.observerNext p μ r s) b =
      Prior.prefixMass p μ r (s ++ [b]) := by
  rw [Prior.observerNext, Disjointness.Channel.mass_bind, Finset.mul_sum]
  calc
    _ = ∑ xy, mass μ xy *
        (Protocol.reach p r xy.1 xy.2 s * mass (Protocol.next p r xy.1 xy.2 s) b) := by
      apply Finset.sum_congr rfl
      intro xy _
      rw [← mul_assoc, Prior.weighted_posterior]
      ring
    _ = _ := by
      simp only [Protocol.weighted_mass_next p r _ _ s who howner b]
      exact (Prior.prefixMass_eq_sum p μ r (s ++ [b])).symm

theorem active_of_not_halt (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (s : List Bool)
    (hs : halt p μ r v xy β s = false) : ∃ who, Tree.speaker (p.tree r) s = some who := by
  have hn : Tree.speaker (p.tree r) s ≠ none := by
    simp only [halt, decide_eq_false_iff_not, not_or] at hs
    exact hs.1
  exact Option.ne_none_iff_exists'.mp hn

theorem halt_transcript (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (x : X) (y : Y) (ω : SA × SB) :
    halt p μ r v xy β (Prefix.Experiment.transcript p r x y ω) = true := by
  have hh := (Tree.speaker_take_eq_none_iff (p.tree r) (x,ω.1) (y,ω.2)
    ((p.tree r).run (x,ω.1) (y,ω.2)).1.length).mpr le_rfl
  simp only [List.take_length] at hh
  simp [halt, Experiment.transcript, hh]

noncomputable def observerLaw (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) : PMF (List Bool) :=
  StoppingFrontier.law (p.tree r).depth (halt p μ r v xy β) (Prior.observerNext p μ r) v

noncomputable def aliceLaw (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) : PMF (List Bool) :=
  StoppingFrontier.law (p.tree r).depth (halt p μ r v xy β) (aliceKernel p μ r xy.1) v

noncomputable def bobLaw (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) : PMF (List Bool) :=
  StoppingFrontier.law (p.tree r).depth (halt p μ r v xy β) (bobKernel p μ r xy.2) v

noncomputable def targetLaw (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) : PMF (List Bool) :=
  StoppingFrontier.law (p.tree r).depth (halt p μ r v xy β) (targetKernel p μ r xy) v

/-- Equation (8.5), in cross-multiplied form, for the four normalized frontier
laws constructed from the actual protocol. No factorization hypothesis remains. -/
theorem law_factorization (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (w : List Bool) :
    mass (aliceLaw p μ r v xy β) w * mass (bobLaw p μ r v xy β) w =
      mass (observerLaw p μ r v xy β) w * mass (targetLaw p μ r v xy β) w :=
  StoppingFrontier.law_factorization _ _ _ _ _ _ (kernel_factorization p μ r xy) v w

omit [Fintype X] [Fintype Y] in
theorem private_prefixProbability (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool) :
    StoppingFrontier.prefixProbability (Experiment.privateSeeds p)
      (Experiment.transcript p r x y) s = Protocol.reach p r x y s := by
  change mass ((Experiment.privateSeeds p).map (Experiment.history p r x y s.length)) s = _
  rw [Experiment.privateSeeds_history]
  rfl

/-- The target frontier law is the actual private execution conditioned on the
starting prefix and stopped at the first divergence frontier. -/
theorem targetLaw_eq_execution (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ)
    (hv : 0 < Protocol.reach p r xy.1 xy.2 v) :
    targetLaw p μ r v xy β = StoppingFrontier.stoppedExecution (Experiment.privateSeeds p)
      (Experiment.transcript p r xy.1 xy.2) (p.tree r).depth (halt p μ r v xy β) v := by
  apply StoppingFrontier.law_eq_stoppedExecution
  · intro s hs b
    obtain ⟨who,howner⟩ := active_of_not_halt p μ r v xy β s hs
    simp only [private_prefixProbability]
    exact weighted_targetKernel p μ r xy s who howner b
  · rwa [private_prefixProbability]
  · intro ω
    exact Disjointness.Tree.run_length_le_depth _ _ _
  · exact halt_transcript p μ r v xy β xy.1 xy.2

/-- The observer frontier law is the corresponding actual conditional
input/private-seed mixture, stopped at the identical input-dependent frontier. -/
theorem observerLaw_eq_execution (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (hv : 0 < Prior.prefixMass p μ r v) :
    observerLaw p μ r v xy β = StoppingFrontier.stoppedExecution (Prior.execution p μ)
      (fun ω ↦ Experiment.transcript p r ω.1.1 ω.1.2 ω.2)
      (p.tree r).depth (halt p μ r v xy β) v := by
  apply StoppingFrontier.law_eq_stoppedExecution
  · intro s hs b
    obtain ⟨who,howner⟩ := active_of_not_halt p μ r v xy β s hs
    exact weighted_observerKernel p μ r s who howner b
  · exact hv
  · intro ω
    exact Disjointness.Tree.run_length_le_depth _ _ _
  · intro ω
    exact halt_transcript p μ r v xy β ω.1.1 ω.1.2 ω.2

end BBCR.ProtocolFrontier
