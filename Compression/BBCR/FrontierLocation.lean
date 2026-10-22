module

public import BBCR.ProtocolFrontier
public import BBCR.TreeBlocks
public import Mathlib.Data.Nat.Log

/-! An actual binary tree for exchanging the two local frontier indices.
Its cost is explicit: twice the binary length of the public path bound. -/

@[expose] public section

open Disjointness
open scoped Classical

namespace BBCR.FrontierLocation

def first (halt : List Bool → Bool) : List Bool → List Bool → ℕ
  | _, [] => 0
  | s, b :: w => if halt s then 0 else 1 + first halt (s ++ [b]) w

theorem first_le (halt : List Bool → Bool) (s w : List Bool) : first halt s w ≤ w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons b w ih =>
    simp only [first, List.length_cons]
    split_ifs
    · omega
    · exact (Nat.add_le_add_left (ih (s ++ [b])) 1).trans_eq (Nat.add_comm _ _)

theorem first_or (a b : List Bool → Bool) (s w : List Bool) :
    first (fun t ↦ a t || b t) s w = min (first a s w) (first b s w) := by
  induction w generalizing s with
  | nil => rfl
  | cons bit w ih =>
    cases ha : a s <;> cases hb : b s <;> simp [first, ha, hb, ih, Nat.add_min_add_left]

theorem first_eq_hit_length (halt : List Bool → Bool) (n : ℕ) (s w : List Bool)
    (hlen : w.length ≤ n) : first halt s w = (StoppingFrontier.hit n halt s w).length := by
  induction n generalizing s w with
  | zero =>
    have he : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst w
    rfl
  | succ n ih =>
    cases w with
    | nil => simp [first, StoppingFrontier.hit]
    | cons b w =>
      cases hs : halt s <;> simp [first, StoppingFrontier.hit, hs, ih _ w (by simpa using hlen), Nat.add_comm]

theorem take_first_eq_hit (halt : List Bool → Bool) (n : ℕ) (s w : List Bool)
    (hlen : w.length ≤ n) : w.take (first halt s w) = StoppingFrontier.hit n halt s w := by
  induction n generalizing s w with
  | zero =>
    have he : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst w
    rfl
  | succ n ih =>
    cases w with
    | nil => simp [first, StoppingFrontier.hit]
    | cons b w =>
      cases hs : halt s with
      | true => simp [first, StoppingFrontier.hit, hs]
      | false =>
        simp only [first, StoppingFrontier.hit, hs, Bool.false_eq_true, ite_false]
        rw [show 1 + first halt (s ++ [b]) w = first halt (s ++ [b]) w + 1 by omega]
        simp only [List.take_succ_cons, ih _ w (by simpa using hlen)]

def width (C : ℕ) : ℕ := Nat.clog 2 (C + 1)

def encode (C : ℕ) (a : Fin (C + 1)) : Fin (width C) → Bool :=
  fun i ↦ a.val.testBit i.val

theorem encode_injective (C : ℕ) : Function.Injective (encode C) := by
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < width C
  · exact congrFun hab ⟨i,hi⟩
  · have hwi : Nat.clog 2 (C + 1) ≤ i := by
      change width C ≤ i
      omega
    have hpow : C + 1 ≤ 2 ^ i :=
      (Nat.le_pow_clog (by decide : 1 < 2) (C + 1)).trans (Nat.pow_le_pow_right (by decide) hwi)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hpow), Nat.testBit_lt_two_pow (b.isLt.trans_le hpow)]

noncomputable def decode (C : ℕ) : (Fin (width C) → Bool) → Fin (C + 1) :=
  Function.invFun (encode C)

@[simp] theorem decode_encode (C : ℕ) (a : Fin (C + 1)) : decode C (encode C a) = a :=
  Function.leftInverse_invFun (encode_injective C) a

variable {A B : Type*}

/-- Both inputs affect only their owner's block. The public continuation sees
the two decoded indices and hence their minimum. -/
noncomputable def exchange (C : ℕ) (a : A → Fin (C + 1)) (b : B → Fin (C + 1))
    (k : Fin (C + 1) → Fin (C + 1) → Tree A B) : Tree A B :=
  TreeBlocks.alice (width C) (fun x ↦ encode C (a x)) (fun va ↦
    TreeBlocks.bob (width C) (fun y ↦ encode C (b y)) (fun vb ↦ k (decode C va) (decode C vb)))

theorem exchange_run (C : ℕ) (a : A → Fin (C + 1)) (b : B → Fin (C + 1))
    (k : Fin (C + 1) → Fin (C + 1) → Tree A B) (x : A) (y : B) :
    (exchange C a b k).run x y =
      (List.ofFn (encode C (a x)) ++ List.ofFn (encode C (b y)) ++ ((k (a x) (b y)).run x y).1,
        ((k (a x) (b y)).run x y).2) := by
  simp only [exchange, TreeBlocks.run_alice, TreeBlocks.run_bob, decode_encode, List.append_assoc]

theorem exchange_depth (C : ℕ) (a : A → Fin (C + 1)) (b : B → Fin (C + 1))
    (k : Fin (C + 1) → Fin (C + 1) → Tree A B) (d : ℕ)
    (hk : ∀ i j, (k i j).depth ≤ d) : (exchange C a b k).depth ≤ 2 * width C + d := by
  apply (TreeBlocks.depth_alice_le _ _ _ (width C + d) (fun va ↦
    TreeBlocks.depth_bob_le _ _ _ d (fun vb ↦ hk _ _))).trans
  omega

end BBCR.FrontierLocation

namespace BBCR.ProtocolFrontier

variable {X Y R SA SB : Type*} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def aliceStop (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (x : X) (β : ℝ) (s : List Bool) : Bool :=
  decide (Prefix.Tree.speaker (p.tree r) s = none ∨ β ≤ accumulated
    (fun t ↦ if Prefix.Tree.speaker (p.tree r) t = some .alice then
      divergence (Prefix.Protocol.aliceNext p r t x) (Prefix.Prior.observerNext p μ r t) else 0) v.length s)

noncomputable def bobStop (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (y : Y) (β : ℝ) (s : List Bool) : Bool :=
  decide (Prefix.Tree.speaker (p.tree r) s = none ∨ β ≤ accumulated
    (fun t ↦ if Prefix.Tree.speaker (p.tree r) t = some .bob then
      divergence (Prefix.Protocol.bobNext p r t y) (Prefix.Prior.observerNext p μ r t) else 0) v.length s)

/-- Each player computes one stopping index using only their input and the
public candidate path. Their minimum is exactly the common stopping index. -/
theorem halt_local (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (s : List Bool) :
    halt p μ r v xy β s = (aliceStop p μ r v xy.1 β s || bobStop p μ r v xy.2 β s) := by
  simp only [halt, aliceStop, bobStop, Prefix.Prior.aliceDivergence, Prefix.Prior.bobDivergence,
    le_max_iff]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  tauto

theorem frontier_index_min (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (w : List Bool) (hlen : w.length ≤ (p.tree r).depth) :
    (StoppingFrontier.hit (p.tree r).depth (halt p μ r v xy β) v w).length =
      min (FrontierLocation.first (aliceStop p μ r v xy.1 β) v w)
        (FrontierLocation.first (bobStop p μ r v xy.2 β) v w) := by
  rw [← FrontierLocation.first_eq_hit_length _ _ _ _ hlen]
  have he : halt p μ r v xy β = fun s ↦ aliceStop p μ r v xy.1 β s || bobStop p μ r v xy.2 β s := by
    funext s
    exact halt_local p μ r v xy β s
  rw [he, FrontierLocation.first_or]

end BBCR.ProtocolFrontier
