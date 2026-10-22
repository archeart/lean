module

public import BBCR.PrefixInformation
public import Mathlib.Data.List.GetD

/-! Public termination and exact padded-bit chain rules. A padded next bit is
constant after a leaf, and the tree determines from the public history whether
to append it. Thus padding does not introduce any information or communication. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Disjointness
open scoped Classical

namespace BBCR.Prefix.Tree

variable {A B : Type*}

theorem speaker_comap {A' B' : Type*} (t : Disjointness.Tree A B)
    (f : A' → A) (g : B' → B) (s : List Bool) :
    speaker (t.comap f g) s = speaker t s := by
  induction t generalizing s <;> cases s <;> simp_all [Disjointness.Tree.comap, speaker]

theorem speaker_take_eq_none_iff (t : Disjointness.Tree A B) (a : A) (b : B) (k : ℕ) :
    speaker t ((t.run a b).1.take k) = none ↔ (t.run a b).1.length ≤ k := by
  induction t generalizing k with
  | leaf o => simp [Disjointness.Tree.run, speaker]
  | alice q z o hz ho =>
    cases k with
    | zero => simp [speaker, Disjointness.Tree.run]
    | succ k => cases h : q a <;> simp [speaker, Disjointness.Tree.run, h, hz, ho]
  | bob q z o hz ho =>
    cases k with
    | zero => simp [speaker, Disjointness.Tree.run]
    | succ k => cases h : q b <;> simp [speaker, Disjointness.Tree.run, h, hz, ho]

theorem active_history_length (t : Disjointness.Tree A B) (a : A) (b : B) (k : ℕ)
    (h : speaker t ((t.run a b).1.take k) ≠ none) : ((t.run a b).1.take k).length = k := by
  have hn : k < (t.run a b).1.length := by
    exact Nat.lt_of_not_ge (fun hh ↦ h ((speaker_take_eq_none_iff t a b k).mpr hh))
  simp [List.length_take, Nat.min_eq_left hn.le]

theorem message_of_stopped (t : Disjointness.Tree A B) (a : A) (b : B) (k : ℕ)
    (h : speaker t ((t.run a b).1.take k) = none) : (t.run a b).1.getD k false = false :=
  List.getD_eq_default _ _ ((speaker_take_eq_none_iff t a b k).mp h)

/-- Reconstruct the next prefix from the current prefix, its public node, and
the padded next bit. At a leaf the next bit is discarded. -/
theorem take_succ_run (t : Disjointness.Tree A B) (a : A) (b : B) (k : ℕ) :
    (t.run a b).1.take (k + 1) =
      if speaker t ((t.run a b).1.take k) = none then (t.run a b).1.take k
      else (t.run a b).1.take k ++ [(t.run a b).1.getD k false] := by
  by_cases h : speaker t ((t.run a b).1.take k) = none
  · have hn := (speaker_take_eq_none_iff t a b k).mp h
    rw [ite_eq_left h, List.take_of_length_le hn, List.take_of_length_le (hn.trans (Nat.le_succ k))]
  · have hn : k < (t.run a b).1.length := by
      exact Nat.lt_of_not_ge (fun hh ↦ h ((speaker_take_eq_none_iff t a b k).mpr hh))
    rw [ite_eq_right h, List.take_add_one]
    simp [List.getElem?_eq_getElem hn]

end BBCR.Prefix.Tree

namespace BBCR.Prefix.Prior

variable {X Y R SA SB : Type*} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

local instance prefixStructureFiniteRange {E F : Type*} [Finite E] (f : E → F) : FiniteRange f :=
  ⟨Set.finite_range f⟩

noncomputable def stepInformation (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (ν : Measure (Sample X Y SA SB)) (k : ℕ) : ℝ :=
  condMutualInfo Prod.fst (message p r k) (history p r k) ν

theorem information_history_succ (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (ν : Measure (Sample X Y SA SB)) [IsZeroOrProbabilityMeasure ν] (k : ℕ) :
    mutualInfo Prod.fst (history p r (k + 1)) ν =
      mutualInfo Prod.fst (history p r k) ν + stepInformation p r ν k := by
  let f : List Bool → List Bool × Bool := fun l ↦ (l.take k, l.getD k false)
  let g : List Bool × Bool → List Bool := fun z ↦
    if Tree.speaker (p.tree r) z.1 = none then z.1 else z.1 ++ [z.2]
  have hf : (fun ω ↦ (history p r k ω, message p r k ω)) = f ∘ history p r (k + 1) := by
    funext ω
    simp [f, history, message, Experiment.history, Experiment.message,
      List.take_take, List.getD, List.getElem?_take_of_lt (Nat.lt_succ_self k)]
  have hg : history p r (k + 1) = g ∘ (fun ω ↦ (history p r k ω, message p r k ω)) := by
    funext ω
    exact Tree.take_succ_run (p.tree r) (ω.1.1,ω.2.1) (ω.1.2,ω.2.2) k
  rw [information_of_mutually_determined ν Prod.fst _ _ f g hf hg, information_chain]
  rfl

theorem information_history_chain (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (ν : Measure (Sample X Y SA SB)) [IsZeroOrProbabilityMeasure ν] (n : ℕ) :
    mutualInfo Prod.fst (history p r n) ν = ∑ k ∈ Finset.range n, stepInformation p r ν k := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact mutualInfo_const (show Measurable (Prod.fst : Sample X Y SA SB → X × Y) from .of_discrete) []
  | succ n ih => rw [information_history_succ, ih, Finset.sum_range_succ]

end BBCR.Prefix.Prior
