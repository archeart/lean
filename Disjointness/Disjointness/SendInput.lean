module

public import Disjointness.Tree
public import Disjointness.Target
public import Mathlib.Data.Fin.Tuple.Basic

/-! # A protocol that sends Alice's input, then Bob's answer

The explicit answer bit ensures that the output is determined by the public
transcript. This verifies that the finite model can express an ordinary protocol.
-/

@[expose] public section

namespace Disjointness

namespace SendInput

variable {Y : Type*}

/-- Send all of Alice's bits in order, then transmit Bob's computed output bit. -/
def tree : (n : ℕ) → (Bits n → Y → Bool) → Tree (Bits n) Y
  | 0, f => .bob (f Fin.elim0) (.leaf false) (.leaf true)
  | n + 1, f => .alice (fun x ↦ x 0)
      ((tree n (fun x y ↦ f (Fin.cons false x) y)).comap Fin.tail id)
      ((tree n (fun x y ↦ f (Fin.cons true x) y)).comap Fin.tail id)

/-- Communication is exactly `n+1` in the tree-depth convention. -/
theorem depth_tree (n : ℕ) (f : Bits n → Y → Bool) : (tree n f).depth = n + 1 := by
  induction n with
  | zero => simp [tree, Tree.depth]
  | succ n ih => simp [tree, Tree.depth, ih]

/-- The public output equals the desired function on every input. -/
theorem output_tree (n : ℕ) (f : Bits n → Y → Bool) (x : Bits n) (y : Y) :
    ((tree n f).run x y).2 = f x y := by
  induction n with
  | zero =>
      have hx : x = Fin.elim0 := Subsingleton.elim _ _
      subst x
      cases h : f Fin.elim0 y <;> simp [tree, Tree.run, h]
  | succ n ih =>
      have hx := Fin.cons_self_tail x
      cases h : x 0 <;> simp [h] at hx <;>
        simp [tree, Tree.run, h, ih, hx]

end SendInput

/-- A deterministic DISJ protocol represented using singleton random-seed types. -/
noncomputable def sendInputProtocol (n : ℕ) : Protocol (Bits n) (Bits n) Unit Unit Unit where
  publicLaw := PMF.pure ()
  aliceLaw := PMF.pure ()
  bobLaw := PMF.pure ()
  tree := fun _ ↦ (SendInput.tree n disj).comap Prod.fst Prod.fst

theorem sendInputProtocol_cost (n : ℕ) : (sendInputProtocol n).cost = n + 1 := by
  simp [Protocol.cost, sendInputProtocol, SendInput.depth_tree]

theorem sendInputProtocol_outputLaw (n : ℕ) (x y : Bits n) :
    (sendInputProtocol n).outputLaw x y = PMF.pure (disj x y) := by
  simp [Protocol.outputLaw, Protocol.seedLaw, sendInputProtocol, PMF.pure_map,
    SendInput.output_tree]

/-- The model has a zero-error DISJ protocol in every dimension. -/
theorem sendInputProtocol_correct (n : ℕ) : (sendInputProtocol n).Correct disj 0 := by
  intro x y
  simp [Protocol.error, sendInputProtocol_outputLaw, PMF.pure_apply]

end Disjointness
