module

public import BBCR.NoiseCausality

/-! At an active public node, the selected fresh correctness bit toggles the
next transmitted bit. Together with prefix causality, this identifies which
fresh coin controls the actual conditional next-message experiment. -/

@[expose] public section

open Disjointness
open scoped Classical

namespace BBCR.TreeBlocks

variable {A B : Type*}

theorem speaker_alice_prefix (n : ℕ) (q : A → Fin n → Bool)
    (k : (Fin n → Bool) → Disjointness.Tree A B) (s : List Bool) (hs : s.length < n) :
    Prefix.Tree.speaker (alice n q k) s = some .alice := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    cases s with
    | nil => rfl
    | cons bit s =>
      cases bit <;> exact ih _ _ s (by simpa using hs)

theorem speaker_bob_prefix (n : ℕ) (q : B → Fin n → Bool)
    (k : (Fin n → Bool) → Disjointness.Tree A B) (s : List Bool) (hs : s.length < n) :
    Prefix.Tree.speaker (bob n q k) s = some .bob := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    cases s with
    | nil => rfl
    | cons bit s =>
      cases bit <;> exact ih _ _ s (by simpa using hs)

theorem speaker_alice_ofFn_append (n : ℕ) (q : A → Fin n → Bool)
    (k : (Fin n → Bool) → Disjointness.Tree A B) (v : Fin n → Bool) (s : List Bool) :
    Prefix.Tree.speaker (alice n q k) (List.ofFn v ++ s) = Prefix.Tree.speaker (k v) s := by
  induction n with
  | zero =>
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    simp [alice, hv]
  | succ n ih =>
    cases h : v 0 <;> have he := Fin.cons_self_tail v
    all_goals simp only [h] at he
    all_goals change Fin.cons _ (fun i ↦ v i.succ) = v at he
    all_goals simp [alice, Prefix.Tree.speaker, List.ofFn_succ, h, ih, he]

theorem speaker_bob_ofFn_append (n : ℕ) (q : B → Fin n → Bool)
    (k : (Fin n → Bool) → Disjointness.Tree A B) (v : Fin n → Bool) (s : List Bool) :
    Prefix.Tree.speaker (bob n q k) (List.ofFn v ++ s) = Prefix.Tree.speaker (k v) s := by
  induction n with
  | zero =>
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    simp [bob, hv]
  | succ n ih =>
    cases h : v 0 <;> have he := Fin.cons_self_tail v
    all_goals simp only [h] at he
    all_goals change Fin.cons _ (fun i ↦ v i.succ) = v at he
    all_goals simp [bob, Prefix.Tree.speaker, List.ofFn_succ, h, ih, he]

end BBCR.TreeBlocks

namespace BBCR.SmoothingTree

open Prefix

theorem getD_before_block {m : ℕ} (j : Fin m) (v : Fin m → Bool) (rest : List Bool) :
    (List.ofFn v ++ rest).getD j.val false = v j :=
  congrFun (blockVector_append m v rest) j

theorem getD_after_block (m n : ℕ) (v : Fin m → Bool) (rest : List Bool) :
    (List.ofFn v ++ rest).getD (m + n) false = rest.getD n false := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem fresh_message_complement {A B : Type*} (C m : ℕ) (t : Disjointness.Tree A B)
    (level d : ℕ) (hlevel : level + d ≤ C) (j : Fin m) (who : Speaker)
    (a : A) (b : B) (ta tb : Tape C m)
    (howner : Prefix.Tree.speaker (smooth C m level t)
      (((smooth C m level t).run (a,ta) (b,tb)).1.take (d * m + j.val)) = some who) :
    (((smooth C m level t).run
      (a, modifyTape who .alice ta (tapeIndex C (level + d)) j false)
      (b, modifyTape who .bob tb (tapeIndex C (level + d)) j false)).1).getD (d * m + j.val) false =
    !((((smooth C m level t).run
      (a, modifyTape who .alice ta (tapeIndex C (level + d)) j true)
      (b, modifyTape who .bob tb (tapeIndex C (level + d)) j true)).1).getD (d * m + j.val) false) := by
  induction t generalizing level d with
  | leaf o => simp [smooth, Disjointness.Tree.run, Prefix.Tree.speaker] at howner
  | alice q z o hz ho =>
    cases d with
    | zero =>
      simp only [smooth, TreeBlocks.run_alice, Nat.zero_mul, Nat.zero_add,
        take_before_block] at howner
      rw [TreeBlocks.speaker_alice_prefix _ _ _ _ (by simp)] at howner
      have hw : who = .alice := (Option.some.inj howner).symm
      subst who
      rw [smooth, TreeBlocks.run_alice, TreeBlocks.run_alice]
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, getD_before_block,
        modifyTape, ite_true, updateBit_at, encode]
      cases q a <;> rfl
    | succ d =>
      have ht := tapeIndex_ne_later C level d hlevel
      have ha (bit : Bool) := modifyTape_other_block who .alice ta (tapeIndex C (level + (d + 1)))
        (tapeIndex C level) j bit ht
      have hn : (d + 1) * m + j.val = m + (d * m + j.val) := by rw [Nat.succ_mul]; omega
      simp only [smooth, TreeBlocks.run_alice, hn, take_after_block,
        TreeBlocks.speaker_alice_ofFn_append] at howner
      rw [smooth, TreeBlocks.run_alice, TreeBlocks.run_alice]
      simp only [ha, hn, getD_after_block]
      have hi : tapeIndex C (level + (d + 1)) = tapeIndex C ((level + 1) + d) := by congr 1; omega
      rw [hi]
      cases hmaj : majority (encode (q a) (ta (tapeIndex C level)))
      · simp only [hmaj, Bool.false_eq_true, ite_false] at howner ⊢
        exact hz (level + 1) d (by omega) howner
      · simp only [hmaj, ite_true] at howner ⊢
        exact ho (level + 1) d (by omega) howner
  | bob q z o hz ho =>
    cases d with
    | zero =>
      simp only [smooth, TreeBlocks.run_bob, Nat.zero_mul, Nat.zero_add,
        take_before_block] at howner
      rw [TreeBlocks.speaker_bob_prefix _ _ _ _ (by simp)] at howner
      have hw : who = .bob := (Option.some.inj howner).symm
      subst who
      rw [smooth, TreeBlocks.run_bob, TreeBlocks.run_bob]
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, getD_before_block,
        modifyTape, ite_true, updateBit_at, encode]
      cases q b <;> rfl
    | succ d =>
      have ht := tapeIndex_ne_later C level d hlevel
      have hb (bit : Bool) := modifyTape_other_block who .bob tb (tapeIndex C (level + (d + 1)))
        (tapeIndex C level) j bit ht
      have hn : (d + 1) * m + j.val = m + (d * m + j.val) := by rw [Nat.succ_mul]; omega
      simp only [smooth, TreeBlocks.run_bob, hn, take_after_block,
        TreeBlocks.speaker_bob_ofFn_append] at howner
      rw [smooth, TreeBlocks.run_bob, TreeBlocks.run_bob]
      simp only [hb, hn, getD_after_block]
      have hi : tapeIndex C (level + (d + 1)) = tapeIndex C ((level + 1) + d) := by congr 1; omega
      rw [hi]
      cases hmaj : majority (encode (q b) (tb (tapeIndex C level)))
      · simp only [hmaj, Bool.false_eq_true, ite_false] at howner ⊢
        exact hz (level + 1) d (by omega) howner
      · simp only [hmaj, ite_true] at howner ⊢
        exact ho (level + 1) d (by omega) howner

end BBCR.SmoothingTree
