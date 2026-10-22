module

public import BBCR.InternalMistakes
public import BBCR.ProtocolIteration
public import BBCR.ResidualInformation

/-! A finite public table realizes the common-threshold predictions. Following
the speaker's prediction samples the original private-coin transcript exactly. -/

@[expose] public section

open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR.InternalSampling

open Prefix FiniteAzuma InternalPrediction

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable local instance : DecidableEq (X ⊕ Y) := Classical.decEq _

abbrev Row (X Y : Type) (C : ℕ) := BoundedHistory.State C → X ⊕ Y → Bool
abbrev Tape (X Y : Type) (C n : ℕ) := Fin n → Row X Y C

noncomputable def rowLaw (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (C : ℕ) : PMF (Row X Y C) := pi (fun s ↦ coupledNode p μ r s.1)

noncomputable def tapeLaw (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (C n : ℕ) : PMF (Tape X Y C n) :=
  (Process.iid (rowLaw p μ r C) (fun _ ↦ 0) 0 0 n).law

theorem tapeLaw_succ (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (C n : ℕ) : tapeLaw p μ r C (n + 1) =
    (rowLaw p μ r C).bind (fun row ↦ (tapeLaw p μ r C n).map
      (fun rest : Tape X Y C n ↦ Fin.cons row rest)) := rfl

noncomputable def read (C : ℕ) (row : Row X Y C) (s : List Bool) : X ⊕ Y → Bool :=
  if hs : s.length ≤ C then row ⟨s,hs⟩ else fun _ ↦ false

noncomputable def ownerBit (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (C : ℕ) (s : List Bool) (row : Row X Y C) : Bool :=
  match Tree.speaker (p.tree r) s with
  | some .alice => read C row s (.inl xy.1)
  | some .bob => read C row s (.inr xy.2)
  | none => false

noncomputable def trace (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (C : ℕ) : (n : ℕ) → Tape X Y C n → List Bool → List Bool
  | 0, _, _ => []
  | n + 1, tape, s => if LikelihoodFrontier.terminal p r s then [] else
      let b := ownerBit p r xy C s (tape 0)
      b :: trace p r xy C n (Fin.tail tape) (s ++ [b])

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem trace_length (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (C n : ℕ) (tape : Tape X Y C n) (s : List Bool) :
    (trace p r xy C n tape s).length ≤ n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [trace]
    split_ifs
    · simp
    · simpa using Nat.succ_le_succ (ih _ _)

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem trace_mem (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (C n : ℕ) (tape : Tape X Y C n) (s : List Bool) :
    trace p r xy C n tape s ∈ StoppingFrontier.paths n (LikelihoodFrontier.terminal p r) s := by
  induction n generalizing s with
  | zero => simp [trace,StoppingFrontier.paths]
  | succ n ih =>
    cases hn : LikelihoodFrontier.terminal p r s with
    | true => simp [trace,StoppingFrontier.paths,hn]
    | false =>
      have hh := ih (Fin.tail tape) (s ++ [ownerBit p r xy C s (tape 0)])
      cases hb : ownerBit p r xy C s (tape 0) <;>
        simpa [trace,StoppingFrontier.paths,hn,hb] using hh

theorem ownerBit_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (C : ℕ) (s : List Bool) (hs : s.length ≤ C)
    (hn : LikelihoodFrontier.terminal p r s = false) :
    (rowLaw p μ r C).map (ownerBit p r xy C s) = ProtocolFrontier.targetKernel p μ r xy s := by
  have he := ProtocolIteration.pi_eval (fun t : BoundedHistory.State C ↦ coupledNode p μ r t.1) ⟨s,hs⟩
  have hm (i : X ⊕ Y) : (rowLaw p μ r C).map (fun row ↦ read C row s i) = kernels p μ r s i := by
    have hh := congrArg (fun q ↦ q.map (fun row ↦ row i)) he
    rw [PMF.map_comp,coupledNode_marginal] at hh
    simpa only [rowLaw,read,dite_eq_left hs,Function.comp_def] using hh
  have hnone : Tree.speaker (p.tree r) s ≠ none := by simpa [LikelihoodFrontier.terminal] using hn
  obtain ⟨who,hw⟩ := Option.ne_none_iff_exists'.mp hnone
  cases who
  · change (rowLaw p μ r C).map (fun row ↦ ownerBit p r xy C s row) = _
    simpa only [ownerBit,hw,ProtocolFrontier.targetKernel,kernels,Sum.elim_inl,alice] using hm (.inl xy.1)
  · change (rowLaw p μ r C).map (fun row ↦ ownerBit p r xy C s row) = _
    simpa only [ownerBit,hw,ProtocolFrontier.targetKernel,kernels,Sum.elim_inr,bob] using hm (.inr xy.2)

theorem trace_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (C n : ℕ) (s : List Bool) (hs : s.length + n ≤ C) :
    (tapeLaw p μ r C n).map (fun tape ↦ trace p r xy C n tape s) =
      StoppingFrontier.law n (LikelihoodFrontier.terminal p r) (ProtocolFrontier.targetKernel p μ r xy) s := by
  induction n generalizing s with
  | zero => simp [tapeLaw,Process.iid,Process.law,trace,StoppingFrontier.law,PMF.pure_map]
  | succ n ih =>
    cases hn : LikelihoodFrontier.terminal p r s with
    | true =>
      have ht : (fun tape ↦ trace p r xy C (n + 1) tape s) = fun _ ↦ [] := by funext tape; simp [trace,hn]
      rw [ht,map_constant]
      simp [StoppingFrontier.law,hn]
    | false =>
      rw [tapeLaw_succ,PMF.map_bind]
      have hi (row : Row X Y C) :
          ((tapeLaw p μ r C n).map (Fin.cons row)).map (fun tape ↦ trace p r xy C (n + 1) tape s) =
          (StoppingFrontier.law n (LikelihoodFrontier.terminal p r) (ProtocolFrontier.targetKernel p μ r xy)
            (s ++ [ownerBit p r xy C s row])).map (ownerBit p r xy C s row :: ·) := by
        have hh := congrArg (fun q ↦ q.map (ownerBit p r xy C s row :: ·))
          (ih (s ++ [ownerBit p r xy C s row]) (by simp only [List.length_append,List.length_singleton]; omega))
        simpa only [PMF.map_comp,Function.comp_def,trace,hn,Bool.false_eq_true,ite_false,
          Fin.cons_zero,Fin.tail_cons] using hh
      simp_rw [hi]
      rw [StoppingFrontier.law,hn]
      simp only [Bool.false_eq_true,ite_false]
      have hh := congrArg (fun q : PMF Bool ↦ q.bind (fun b ↦
        (StoppingFrontier.law n (LikelihoodFrontier.terminal p r) (ProtocolFrontier.targetKernel p μ r xy)
          (s ++ [b])).map (b :: ·))) (ownerBit_law p μ r xy C s (by omega) hn)
      simpa only [PMF.bind_map,Function.comp_def] using hh

variable [Fintype R]

theorem truePath_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) :
    (tapeLaw p μ r p.cost p.cost).map (fun tape ↦ trace p r xy p.cost p.cost tape []) =
      (Experiment.privateSeeds p).map (Experiment.transcript p r xy.1 xy.2) := by
  rw [trace_law p μ r xy p.cost p.cost [] (by simp)]
  have hpos : 0 < StoppingFrontier.prefixProbability (Experiment.privateSeeds p)
      (Experiment.transcript p r xy.1 xy.2) [] := by
    simp [StoppingFrontier.prefixProbability,map_constant,mass]
  rw [StoppingFrontier.law_eq_stoppedExecution (Experiment.privateSeeds p)
    (Experiment.transcript p r xy.1 xy.2) p.cost (LikelihoodFrontier.terminal p r)
    (ProtocolFrontier.targetKernel p μ r xy) ?_ [] hpos ?_ ?_]
  · simp only [StoppingFrontier.stoppedExecution,List.length_nil,List.take_zero,List.drop_zero,
      FiniteCondition.law_const]
    congr 1
    funext ω
    apply StoppingFrontier.hit_eq_self
    · exact (Disjointness.Tree.run_length_le_depth _ _ _).trans (p.depth_le_cost r)
    · intro j hj
      have hn : Tree.speaker (p.tree r) ((Experiment.transcript p r xy.1 xy.2 ω).take j) ≠ none := by
        intro hh
        exact Nat.not_le_of_gt hj ((Tree.speaker_take_eq_none_iff (p.tree r) (xy.1,ω.1) (xy.2,ω.2) j).mp hh)
      simp [LikelihoodFrontier.terminal,hn]
  · intro s hs b
    have hn : Tree.speaker (p.tree r) s ≠ none := by simpa [LikelihoodFrontier.terminal] using hs
    obtain ⟨who,hw⟩ := Option.ne_none_iff_exists'.mp hn
    simp only [ProtocolFrontier.private_prefixProbability]
    exact ProtocolFrontier.weighted_targetKernel p μ r xy s who hw b
  · intro ω
    exact (Disjointness.Tree.run_length_le_depth _ _ _).trans (p.depth_le_cost r)
  · intro ω
    have hn := (Tree.speaker_take_eq_none_iff (p.tree r) (xy.1,ω.1) (xy.2,ω.2)
      ((p.tree r).run (xy.1,ω.1) (xy.2,ω.2)).1.length).mpr le_rfl
    simp only [List.take_length] at hn
    exact decide_eq_true hn

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem transcript_mem_cost (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (ω : SA × SB) :
    Experiment.transcript p r xy.1 xy.2 ω ∈ StoppingFrontier.paths p.cost (LikelihoodFrontier.terminal p r) [] := by
  have hlen : (Experiment.transcript p r xy.1 xy.2 ω).length ≤ p.cost :=
    (Disjointness.Tree.run_length_le_depth _ _ _).trans (p.depth_le_cost r)
  have he : StoppingFrontier.hit p.cost (LikelihoodFrontier.terminal p r) []
      (Experiment.transcript p r xy.1 xy.2 ω) = Experiment.transcript p r xy.1 xy.2 ω := by
    apply StoppingFrontier.hit_eq_self _ _ _ _ hlen
    intro j hj
    have hn : Tree.speaker (p.tree r) ((Experiment.transcript p r xy.1 xy.2 ω).take j) ≠ none := by
      intro hh
      exact Nat.not_le_of_gt hj ((Tree.speaker_take_eq_none_iff (p.tree r) (xy.1,ω.1) (xy.2,ω.2) j).mp hh)
    simp [LikelihoodFrontier.terminal,hn]
  rw [← he]
  apply StoppingFrontier.hit_mem _ _ _ _ hlen
  have hn := (Tree.speaker_take_eq_none_iff (p.tree r) (xy.1,ω.1) (xy.2,ω.2)
    ((p.tree r).run (xy.1,ω.1) (xy.2,ω.2)).1.length).mpr le_rfl
  simp only [List.take_length] at hn
  apply decide_eq_true
  simpa only [List.nil_append,Experiment.transcript] using hn

noncomputable def actualLeaf (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (ω : SA × SB) : ↥(StoppingFrontier.paths p.cost (LikelihoodFrontier.terminal p r) []) :=
  ⟨Experiment.transcript p r xy.1 xy.2 ω,transcript_mem_cost p r xy ω⟩

theorem leaf_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) :
    StoppingFrontier.finiteLaw p.cost (LikelihoodFrontier.terminal p r) (ProtocolFrontier.targetKernel p μ r xy) [] =
      (Experiment.privateSeeds p).map (actualLeaf p r xy) := by
  apply StoppedAzuma.map_subtype_injective
  rw [StoppingFrontier.finiteLaw_map_val,PMF.map_comp]
  exact (trace_law p μ r xy p.cost p.cost [] (by simp)).symm.trans (truePath_law p μ r xy)

end BBCR.InternalSampling
