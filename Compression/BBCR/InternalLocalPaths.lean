module

public import BBCR.InternalSamplingCost
public import BBCR.LikelihoodSimulator

/-! The two local paths agree with the speaker path whenever its public table
contains no disagreement. This supplies the zero-communication branch. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.InternalSampling

open Prefix

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def localTrace (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (i : X ⊕ Y) (C : ℕ) : (n : ℕ) → Tape X Y C n → List Bool → List Bool
  | 0, _, _ => []
  | n + 1, tape, s => if LikelihoodFrontier.terminal p r s then [] else
      let b := read C (tape 0) s i
      b :: localTrace p r i C n (Fin.tail tape) (s ++ [b])

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem mistakes_zero_or_one_le (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (C n : ℕ) (tape : Tape X Y C n) (s : List Bool) :
    mistakes p r xy C n tape s = 0 ∨ 1 ≤ mistakes p r xy C n tape s := by
  induction n generalizing s with
  | zero => exact Or.inl rfl
  | succ n ih =>
    by_cases hn : LikelihoodFrontier.terminal p r s = true
    · exact Or.inl (by simp [mistakes,hn])
    · have htail := ih (Fin.tail tape) (s ++ [ownerBit p r xy C s (tape 0)])
      have hnonneg := mistakes_nonneg p r xy C n (Fin.tail tape) (s ++ [ownerBit p r xy C s (tape 0)])
      by_cases hh : read C (tape 0) s (.inl xy.1) = read C (tape 0) s (.inr xy.2)
      · simpa [mistakes,hn,flag,hh] using htail
      · exact Or.inr (by simpa [mistakes,hn,flag,hh] using hnonneg)

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem localTrace_eq_of_zero (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (C n : ℕ) (tape : Tape X Y C n) (s : List Bool)
    (h : mistakes p r xy C n tape s = 0) :
    localTrace p r (.inl xy.1) C n tape s = trace p r xy C n tape s ∧
      localTrace p r (.inr xy.2) C n tape s = trace p r xy C n tape s := by
  induction n generalizing s with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    cases hn : LikelihoodFrontier.terminal p r s with
    | true => simp [localTrace,trace,hn]
    | false =>
      have hz : flag C s xy (tape 0) + mistakes p r xy C n (Fin.tail tape)
          (s ++ [ownerBit p r xy C s (tape 0)]) = 0 := by simpa [mistakes,hn] using h
      have hnonneg := mistakes_nonneg p r xy C n (Fin.tail tape) (s ++ [ownerBit p r xy C s (tape 0)])
      have hf : flag C s xy (tape 0) = 0 := by
        have hflag : 0 ≤ flag C s xy (tape 0) := by unfold flag; split_ifs <;> norm_num
        linarith
      have he : read C (tape 0) s (.inl xy.1) = read C (tape 0) s (.inr xy.2) := by
        by_contra hh
        simp [flag,hh] at hf
      have ht : mistakes p r xy C n (Fin.tail tape) (s ++ [ownerBit p r xy C s (tape 0)]) = 0 := by linarith
      have hi := ih (Fin.tail tape) _ ht
      have hb : ownerBit p r xy C s (tape 0) = read C (tape 0) s (.inl xy.1) := by
        have hw : Tree.speaker (p.tree r) s ≠ none := by simpa [LikelihoodFrontier.terminal] using hn
        obtain ⟨who,hw⟩ := Option.ne_none_iff_exists'.mp hw
        cases who <;> simp [ownerBit,hw,he]
      simp only [localTrace,trace,hn,Bool.false_eq_true,ite_false,hb] at hi ⊢
      exact ⟨congrArg (read C (tape 0) s (.inl xy.1) :: ·) hi.1,
        by rw [← he]; exact congrArg (read C (tape 0) s (.inl xy.1) :: ·) hi.2⟩

noncomputable def view (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) : p.View :=
  ⟨r,if h : s ∈ (p.tree r).leafPaths then ⟨s,h⟩ else
    ⟨TreeTrace.firstLeaf (p.tree r),TreeTrace.firstLeaf_mem _⟩⟩

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem view_transcript (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (ω : SA × SB) :
    view p r (Experiment.transcript p r xy.1 xy.2 ω) = p.runView xy.1 xy.2 (r,ω) := by
  have hm := Disjointness.Tree.run_mem_leafPaths (p.tree r) (xy.1,ω.1) (xy.2,ω.2)
  dsimp only [view,Experiment.transcript,Disjointness.Protocol.runView]
  split_ifs
  rfl

variable [Fintype R]

theorem trueView_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) :
    (tapeLaw p μ r p.cost p.cost).map (fun tape ↦ view p r (trace p r xy p.cost p.cost tape [])) =
      LikelihoodFrontier.conditionalViewLaw p r xy := by
  have hh := congrArg (fun q : PMF (List Bool) ↦ q.map (view p r)) (truePath_law p μ r xy)
  simpa only [PMF.map_comp,Function.comp_def,view_transcript,LikelihoodFrontier.conditionalViewLaw] using hh

end BBCR.InternalSampling
