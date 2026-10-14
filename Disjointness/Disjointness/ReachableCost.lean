module

public import Disjointness.LowerBound

/-! Remove unreachable deep branches by truncating trees at an execution-length bound. -/

@[expose] public section

namespace Disjointness.Tree

variable {A B : Type*}

/-- Cut a tree after at most `c` communicated bits. Existing leaves retain their labels. -/
def truncate : ℕ → Tree A B → Tree A B
  | _, .leaf b => .leaf b
  | 0, _ => .leaf false
  | c + 1, .alice q z o => .alice q (truncate c z) (truncate c o)
  | c + 1, .bob q z o => .bob q (truncate c z) (truncate c o)

theorem depth_truncate_le (c : ℕ) (t : Tree A B) : (t.truncate c).depth ≤ c := by
  induction c generalizing t with
  | zero => cases t <;> simp [truncate, depth]
  | succ c ih => cases t <;> simp [truncate, depth, ih]

/-- Truncation preserves every execution that already terminates within the bound. -/
theorem run_truncate (c : ℕ) (t : Tree A B) (a : A) (b : B)
    (h : (t.run a b).1.length ≤ c) : (t.truncate c).run a b = t.run a b := by
  induction c generalizing t with
  | zero =>
    cases t with
    | leaf o => rfl
    | alice q z o => cases hb : q a <;> simp [run, hb] at h
    | bob q z o => cases hb : q b <;> simp [run, hb] at h
  | succ c ih =>
    cases t with
    | leaf o => rfl
    | alice q z o =>
      cases hb : q a <;> simp only [run, hb, Bool.false_eq_true, ite_false, ite_true,
        List.length_cons, Nat.add_le_add_iff_right] at h
      all_goals simp [truncate, run, hb, ih _ h]
    | bob q z o =>
      cases hb : q b <;> simp only [run, hb, Bool.false_eq_true, ite_false, ite_true,
        List.length_cons, Nat.add_le_add_iff_right] at h
      all_goals simp [truncate, run, hb, ih _ h]

end Disjointness.Tree

namespace Disjointness.Protocol

variable {X Y R SA SB : Type*}

def truncate (p : Protocol X Y R SA SB) (c : ℕ) : Protocol X Y R SA SB :=
  { p with tree := fun r ↦ (p.tree r).truncate c }

theorem truncate_cost_le [Fintype R] (p : Protocol X Y R SA SB) (c : ℕ) :
    (p.truncate c).cost ≤ c := by
  apply Finset.sup_le
  intro r _
  exact Tree.depth_truncate_le c _

theorem truncate_outputLaw (p : Protocol X Y R SA SB) (c : ℕ)
    (h : ∀ x y r a b, ((p.tree r).run (x,a) (y,b)).1.length ≤ c) (x : X) (y : Y) :
    (p.truncate c).outputLaw x y = p.outputLaw x y := by
  unfold outputLaw
  congr 1
  funext s
  exact congrArg Prod.snd (Tree.run_truncate c (p.tree s.1) (x,s.2.1) (y,s.2.2)
    (h x y s.1 s.2.1 s.2.2))

theorem truncate_correct (p : Protocol X Y R SA SB) (c : ℕ)
    (h : ∀ x y r a b, ((p.tree r).run (x,a) (y,b)).1.length ≤ c)
    {f : X → Y → Bool} {ε : ℝ} (hc : p.Correct f ε) : (p.truncate c).Correct f ε := by
  intro x y
  simpa only [error, p.truncate_outputLaw c h] using hc x y

end Disjointness.Protocol

namespace Disjointness

/-- The finite-model lower bound also applies to any bound on reachable
execution lengths, regardless of unreachable branches in the original trees. -/
theorem disjointness_lower_bound_of_length {n : ℕ} {R SA SB : Type*}
    [Fintype R] [Fintype SA] [Fintype SB]
    (p : Protocol (Bits n) (Bits n) R SA SB) (c : ℕ)
    (h : ∀ x y r a b, ((p.tree r).run (x,a) (y,b)).1.length ≤ c)
    (hc : p.Correct disj (1 / 3)) : lowerBoundConstant * (n : ℝ) ≤ (c : ℝ) := by
  exact (disjointness_lower_bound (p.truncate c) (p.truncate_correct c h hc)).trans
    (by exact_mod_cast p.truncate_cost_le c)

end Disjointness
