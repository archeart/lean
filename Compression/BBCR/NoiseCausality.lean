module

public import BBCR.NoiseResampling
public import BBCR.PrefixStructure
public import Mathlib.Data.Fin.Tuple.Take

/-! A fresh correctness bit at logical block `level+d` cannot affect the
preceding `d*m+j` physical messages. These are pointwise execution statements,
before any probability or independence argument is invoked. -/

@[expose] public section

open Disjointness
open scoped Classical

namespace BBCR.SmoothingTree

open Prefix

def modifyTape {C m : ℕ} (who owner : Speaker) (tape : Tape C m)
    (i : Fin (C + 1)) (j : Fin m) (bit : Bool) : Tape C m :=
  if who = owner then updateBit tape i j bit else tape

theorem modifyTape_other_block {C m : ℕ} (who owner : Speaker) (tape : Tape C m)
    (i i' : Fin (C + 1)) (j : Fin m) (bit : Bool) (h : i' ≠ i) :
    modifyTape who owner tape i j bit i' = tape i' := by
  unfold modifyTape
  split_ifs
  · exact updateBit_other_block tape i i' j bit h
  · rfl

theorem modifyTape_before {C m : ℕ} (who owner : Speaker) (tape : Tape C m)
    (i : Fin (C + 1)) (j k : Fin m) (bit : Bool) (hk : k.val < j.val) :
    modifyTape who owner tape i j bit i k = tape i k := by
  unfold modifyTape
  split_ifs
  · simp only [updateBit, Function.update_self]
    exact Function.update_of_ne (show k ≠ j from fun h ↦ by rw [h] at hk; omega) _ _
  · rfl

theorem take_ofFn_eq {m : ℕ} (j : Fin m) (v w : Fin m → Bool)
    (h : ∀ i : Fin m, i.val < j.val → v i = w i) :
    (List.ofFn v).take j.val = (List.ofFn w).take j.val := by
  rw [← Fin.ofFn_take_eq_take_ofFn j.isLt.le, ← Fin.ofFn_take_eq_take_ofFn j.isLt.le]
  congr 1
  funext i
  exact h _ i.isLt

theorem take_before_block {m : ℕ} (j : Fin m) (v : Fin m → Bool) (rest : List Bool) :
    (List.ofFn v ++ rest).take j.val = (List.ofFn v).take j.val := by
  simp [List.take_append, Nat.sub_eq_zero_of_le j.isLt.le]

theorem take_after_block (m n : ℕ) (v : Fin m → Bool) (rest : List Bool) :
    (List.ofFn v ++ rest).take (m + n) = List.ofFn v ++ rest.take n := by
  rw [List.take_append]
  simp

theorem tapeIndex_ne_later (C level d : ℕ) (h : level + (d + 1) ≤ C) :
    tapeIndex C level ≠ tapeIndex C (level + (d + 1)) := by
  intro he
  have hv := congrArg Fin.val he
  simp only [tapeIndex, Nat.min_eq_left (show level ≤ C by omega), Nat.min_eq_left h] at hv
  omega

/-- Replacing a correctness bit at physical time `d*m+j` preserves all earlier
messages, even on executions that already terminated before that time. -/
theorem fresh_prefix {A B : Type*} (C m : ℕ) (t : Disjointness.Tree A B)
    (level d : ℕ) (hlevel : level + d ≤ C) (j : Fin m) (who : Speaker)
    (a : A) (b : B) (ta tb : Tape C m) (bit : Bool) :
    (((smooth C m level t).run
      (a, modifyTape who .alice ta (tapeIndex C (level + d)) j bit)
      (b, modifyTape who .bob tb (tapeIndex C (level + d)) j bit)).1).take (d * m + j.val) =
      (((smooth C m level t).run (a,ta) (b,tb)).1).take (d * m + j.val) := by
  induction t generalizing level d with
  | leaf o => simp [smooth, Disjointness.Tree.run]
  | alice q z o hz ho =>
    cases d with
    | zero =>
      rw [smooth, TreeBlocks.run_alice, TreeBlocks.run_alice]
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, take_before_block]
      apply take_ofFn_eq
      intro i hi
      simp only [encode]
      rw [modifyTape_before who .alice ta (tapeIndex C level) j i bit hi]
    | succ d =>
      have ht := tapeIndex_ne_later C level d hlevel
      have ha := modifyTape_other_block who .alice ta (tapeIndex C (level + (d + 1)))
        (tapeIndex C level) j bit ht
      rw [smooth, TreeBlocks.run_alice, TreeBlocks.run_alice]
      simp only [ha]
      have hn : (d + 1) * m + j.val = m + (d * m + j.val) := by rw [Nat.succ_mul]; omega
      rw [hn, take_after_block, take_after_block]
      congr 1
      have hi : tapeIndex C (level + (d + 1)) = tapeIndex C ((level + 1) + d) := by congr 1; omega
      rw [hi]
      cases majority (encode (q a) (ta (tapeIndex C level)))
      · exact hz (level + 1) d (by omega)
      · exact ho (level + 1) d (by omega)
  | bob q z o hz ho =>
    cases d with
    | zero =>
      rw [smooth, TreeBlocks.run_bob, TreeBlocks.run_bob]
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, take_before_block]
      apply take_ofFn_eq
      intro i hi
      simp only [encode]
      rw [modifyTape_before who .bob tb (tapeIndex C level) j i bit hi]
    | succ d =>
      have ht := tapeIndex_ne_later C level d hlevel
      have hb := modifyTape_other_block who .bob tb (tapeIndex C (level + (d + 1)))
        (tapeIndex C level) j bit ht
      rw [smooth, TreeBlocks.run_bob, TreeBlocks.run_bob]
      simp only [hb]
      have hn : (d + 1) * m + j.val = m + (d * m + j.val) := by rw [Nat.succ_mul]; omega
      rw [hn, take_after_block, take_after_block]
      congr 1
      have hi : tapeIndex C (level + (d + 1)) = tapeIndex C ((level + 1) + d) := by congr 1; omega
      rw [hi]
      cases majority (encode (q b) (tb (tapeIndex C level)))
      · exact hz (level + 1) d (by omega)
      · exact ho (level + 1) d (by omega)

end BBCR.SmoothingTree
