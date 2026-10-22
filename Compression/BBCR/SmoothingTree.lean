module

public import BBCR.TreeBlocks

/-! The actual local tree transformation for noisy-block smoothing. This file
proves cost and pointwise transcript recovery, separately from probability and
information-cost estimates for the random noise tapes. -/

@[expose] public section

open Disjointness
open scoped Classical

namespace BBCR.SmoothingTree

def ones {n : ℕ} (v : Fin n → Bool) : ℕ := ∑ i, if v i then 1 else 0

def majority {n : ℕ} (v : Fin n → Bool) : Bool := decide (n < 2 * ones v)

def encode {n : ℕ} (b : Bool) (noise : Fin n → Bool) : Fin n → Bool :=
  fun i ↦ if noise i then b else !b

@[simp] theorem encode_true {n : ℕ} (noise : Fin n → Bool) : encode true noise = noise := by
  funext i
  simp only [encode]
  cases noise i <;> rfl

@[simp] theorem encode_false {n : ℕ} (noise : Fin n → Bool) :
    encode false noise = (fun i ↦ !(noise i)) := by
  funext i
  simp only [encode]
  cases noise i <;> rfl

theorem ones_complement {n : ℕ} (v : Fin n → Bool) : ones (fun i ↦ !(v i)) + ones v = n := by
  unfold ones
  rw [← Finset.sum_add_distrib]
  have h (i : Fin n) : (if !(v i) then 1 else 0) + (if v i then 1 else 0) = (1 : ℕ) := by
    cases v i <;> rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- A strict majority of correct noise bits decodes either intended bit. -/
theorem majority_encode {n : ℕ} (b : Bool) (noise : Fin n → Bool) (hgood : majority noise = true) :
    majority (encode b noise) = b := by
  have hg : n < 2 * ones noise := by simpa [majority] using hgood
  cases b with
  | true => simpa using hgood
  | false =>
    rw [encode_false]
    have hc := ones_complement noise
    have hn : ¬n < 2 * ones (fun i ↦ !(noise i)) := by omega
    simp [majority, hn]

abbrev Tape (C m : ℕ) := Fin (C + 1) → Fin m → Bool

def tapeIndex (C level : ℕ) : Fin (C + 1) := ⟨min level C, by omega⟩

def GoodTape {C m : ℕ} (tape : Tape C m) : Prop := ∀ i, majority (tape i) = true

def smooth {A B : Type*} (C m level : ℕ) : Tree A B → Tree (A × Tape C m) (B × Tape C m)
  | .leaf o => .leaf o
  | .alice q z o => TreeBlocks.alice m
      (fun a ↦ encode (q a.1) (a.2 (tapeIndex C level)))
      (fun v ↦ if majority v then smooth C m (level + 1) o else smooth C m (level + 1) z)
  | .bob q z o => TreeBlocks.bob m
      (fun b ↦ encode (q b.1) (b.2 (tapeIndex C level)))
      (fun v ↦ if majority v then smooth C m (level + 1) o else smooth C m (level + 1) z)

theorem smooth_depth_le {A B : Type*} (C m level : ℕ) (t : Tree A B) :
    (smooth C m level t).depth ≤ m * t.depth := by
  induction t generalizing level with
  | leaf o => simp [smooth, Tree.depth]
  | alice q z o hz ho =>
    rw [smooth]
    refine (TreeBlocks.depth_alice_le m _ _ (m * max z.depth o.depth) ?_).trans ?_
    · intro v
      split_ifs
      · exact (ho (level + 1)).trans (Nat.mul_le_mul_left m (Nat.le_max_right _ _))
      · exact (hz (level + 1)).trans (Nat.mul_le_mul_left m (Nat.le_max_left _ _))
    · simp [Tree.depth, Nat.mul_add, Nat.add_comm]
  | bob q z o hz ho =>
    rw [smooth]
    refine (TreeBlocks.depth_bob_le m _ _ (m * max z.depth o.depth) ?_).trans ?_
    · intro v
      split_ifs
      · exact (ho (level + 1)).trans (Nat.mul_le_mul_left m (Nat.le_max_right _ _))
      · exact (hz (level + 1)).trans (Nat.mul_le_mul_left m (Nat.le_max_left _ _))
    · simp [Tree.depth, Nat.mul_add, Nat.add_comm]

def logicalTrace {A B : Type*} (C m level : ℕ) : Tree A B → (A × Tape C m) → (B × Tape C m) → List Bool
  | .leaf _, _, _ => []
  | .alice q z o, a, b =>
      let bit := majority (encode (q a.1) (a.2 (tapeIndex C level)))
      bit :: if bit then logicalTrace C m (level + 1) o a b else logicalTrace C m (level + 1) z a b
  | .bob q z o, a, b =>
      let bit := majority (encode (q b.1) (b.2 (tapeIndex C level)))
      bit :: if bit then logicalTrace C m (level + 1) o a b else logicalTrace C m (level + 1) z a b

theorem logicalTrace_of_good {A B : Type*} (C m level : ℕ) (t : Tree A B)
    (a : A) (b : B) (ta tb : Tape C m) (ha : GoodTape ta) (hb : GoodTape tb) :
    logicalTrace C m level t (a,ta) (b,tb) = (t.run a b).1 := by
  induction t generalizing level with
  | leaf o => rfl
  | alice q z o hz ho =>
    simp only [logicalTrace, majority_encode _ _ (ha _), Tree.run]
    cases q a <;> simp [hz, ho]
  | bob q z o hz ho =>
    simp only [logicalTrace, majority_encode _ _ (hb _), Tree.run]
    cases q b <;> simp [hz, ho]

theorem smooth_output_of_good {A B : Type*} (C m level : ℕ) (t : Tree A B)
    (a : A) (b : B) (ta tb : Tape C m) (ha : GoodTape ta) (hb : GoodTape tb) :
    ((smooth C m level t).run (a,ta) (b,tb)).2 = (t.run a b).2 := by
  induction t generalizing level with
  | leaf o => rfl
  | alice q z o hz ho =>
    rw [smooth, TreeBlocks.run_alice]
    simp only [majority_encode _ _ (ha _), Tree.run]
    cases q a <;> simp [hz, ho]
  | bob q z o hz ho =>
    rw [smooth, TreeBlocks.run_bob]
    simp only [majority_encode _ _ (hb _), Tree.run]
    cases q b <;> simp [hz, ho]

/-- Forward encoding uses only the public tree, the original transcript, and
the two noise tapes. It does not inspect either input or original private seed. -/
def encodedTrace {A B : Type*} (C m level : ℕ) :
    Tree A B → List Bool → Tape C m → Tape C m → List Bool
  | .leaf _, _, _, _ => []
  | .alice _ z o, bits, ta, tb =>
      let bit := bits.headD false
      List.ofFn (encode bit (ta (tapeIndex C level))) ++
        if bit then encodedTrace C m (level + 1) o bits.tail ta tb
        else encodedTrace C m (level + 1) z bits.tail ta tb
  | .bob _ z o, bits, ta, tb =>
      let bit := bits.headD false
      List.ofFn (encode bit (tb (tapeIndex C level))) ++
        if bit then encodedTrace C m (level + 1) o bits.tail ta tb
        else encodedTrace C m (level + 1) z bits.tail ta tb

/-- On good tapes the entire physical transcript factors through the original
transcript and independent noise, including for persistent private seeds. -/
theorem run_encodedTrace_of_good {A B : Type*} (C m level : ℕ) (t : Tree A B)
    (a : A) (b : B) (ta tb : Tape C m) (ha : GoodTape ta) (hb : GoodTape tb) :
    ((smooth C m level t).run (a,ta) (b,tb)).1 =
      encodedTrace C m level t (t.run a b).1 ta tb := by
  induction t generalizing level with
  | leaf o => rfl
  | alice q z o hz ho =>
    rw [smooth, TreeBlocks.run_alice]
    simp only [majority_encode _ _ (ha _), Tree.run]
    cases q a <;> simp [encodedTrace, hz, ho]
  | bob q z o hz ho =>
    rw [smooth, TreeBlocks.run_bob]
    simp only [majority_encode _ _ (hb _), Tree.run]
    cases q b <;> simp [encodedTrace, hz, ho]

def blockVector (m : ℕ) (bits : List Bool) : Fin m → Bool := fun i ↦ bits.getD i.val false

def decode {A B : Type*} (m : ℕ) : Tree A B → List Bool → List Bool
  | .leaf _, _ => []
  | .alice _ z o, bits =>
      let bit := majority (blockVector m bits)
      bit :: if bit then decode m o (bits.drop m) else decode m z (bits.drop m)
  | .bob _ z o, bits =>
      let bit := majority (blockVector m bits)
      bit :: if bit then decode m o (bits.drop m) else decode m z (bits.drop m)

/-- Even a malformed physical transcript decodes to an original leaf path;
this makes the public decoder total without any input-dependent fallback. -/
theorem decode_mem_leafPaths {A B : Type*} (m : ℕ) (t : Tree A B) (bits : List Bool) :
    decode m t bits ∈ t.leafPaths := by
  induction t generalizing bits with
  | leaf o => simp [decode, Tree.leafPaths]
  | alice q z o hz ho =>
    simp only [decode]
    cases majority (blockVector m bits) <;> simp [Tree.leafPaths, hz, ho]
  | bob q z o hz ho =>
    simp only [decode]
    cases majority (blockVector m bits) <;> simp [Tree.leafPaths, hz, ho]

theorem blockVector_append (m : ℕ) (v : Fin m → Bool) (rest : List Bool) :
    blockVector m (List.ofFn v ++ rest) = v := by
  funext i
  simp only [blockVector, List.getD]
  rw [List.getElem?_append_left (by simp)]
  simp [i.isLt]

theorem drop_block_append (m : ℕ) (v : Fin m → Bool) (rest : List Bool) :
    (List.ofFn v ++ rest).drop m = rest := by
  simp

/-- Decoding uses only the public tree and communicated noisy transcript. -/
theorem decode_run {A B : Type*} (C m level : ℕ) (t : Tree A B)
    (a : A × Tape C m) (b : B × Tape C m) :
    decode m t ((smooth C m level t).run a b).1 = logicalTrace C m level t a b := by
  induction t generalizing level with
  | leaf o => rfl
  | alice q z o hz ho =>
    rw [smooth, TreeBlocks.run_alice]
    simp only [decode, blockVector_append, logicalTrace]
    rw [drop_block_append]
    cases majority (encode (q a.1) (a.2 (tapeIndex C level))) <;> simp [hz, ho]
  | bob q z o hz ho =>
    rw [smooth, TreeBlocks.run_bob]
    simp only [decode, blockVector_append, logicalTrace]
    rw [drop_block_append]
    cases majority (encode (q b.1) (b.2 (tapeIndex C level))) <;> simp [hz, ho]

theorem decode_run_of_good {A B : Type*} (C m level : ℕ) (t : Tree A B)
    (a : A) (b : B) (ta tb : Tape C m) (ha : GoodTape ta) (hb : GoodTape tb) :
    decode m t ((smooth C m level t).run (a,ta) (b,tb)).1 = (t.run a b).1 := by
  rw [decode_run, logicalTrace_of_good C m level t a b ta tb ha hb]

end BBCR.SmoothingTree
