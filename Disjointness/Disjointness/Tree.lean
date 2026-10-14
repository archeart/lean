module

public import Disjointness.Protocol
public import Mathlib.Data.Finset.Card

/-! # Structural consequences of binary communication trees -/

@[expose] public section

namespace Disjointness.Tree

variable {A B : Type*}

/-- Preprocess each player's input locally. Communication and tree shape are unchanged. -/
def comap {A' B' : Type*} (t : Tree A B) (f : A' → A) (g : B' → B) : Tree A' B' :=
  match t with
  | .leaf output => .leaf output
  | .alice message zero one => .alice (message ∘ f) (zero.comap f g) (one.comap f g)
  | .bob message zero one => .bob (message ∘ g) (zero.comap f g) (one.comap f g)

@[simp]
theorem depth_comap {A' B' : Type*} (t : Tree A B) (f : A' → A) (g : B' → B) :
    (t.comap f g).depth = t.depth := by
  induction t <;> simp_all [comap, depth]

@[simp]
theorem run_comap {A' B' : Type*} (t : Tree A B) (f : A' → A) (g : B' → B)
    (a : A') (b : B') : (t.comap f g).run a b = t.run (f a) (g b) := by
  induction t with
  | leaf output => rfl
  | alice message zero one ihz iho => simp [comap, run, ihz, iho]
  | bob message zero one ihz iho => simp [comap, run, ihz, iho]

/-- Change only the leaf labels, preserving the communicated transcript. -/
def mapOutput (t : Tree A B) (f : Bool → Bool) : Tree A B :=
  match t with
  | .leaf b => .leaf (f b)
  | .alice q z o => .alice q (z.mapOutput f) (o.mapOutput f)
  | .bob q z o => .bob q (z.mapOutput f) (o.mapOutput f)

@[simp] theorem depth_mapOutput (t : Tree A B) (f : Bool → Bool) :
    (t.mapOutput f).depth = t.depth := by
  induction t <;> simp_all [mapOutput, depth]

@[simp] theorem run_mapOutput (t : Tree A B) (f : Bool → Bool) (a : A) (b : B) :
    (t.mapOutput f).run a b = ((t.run a b).1, f (t.run a b).2) := by
  induction t with
  | leaf o => rfl
  | alice q z o hz ho => cases h : q a <;> simp [mapOutput, run, h, hz, ho]
  | bob q z o hz ho => cases h : q b <;> simp [mapOutput, run, h, hz, ho]

/-- Publicly recover the output from a valid leaf transcript. -/
def decode : Tree A B → List Bool → Option Bool
  | .leaf output, [] => some output
  | .leaf _, _ :: _ => none
  | .alice _ _ _, [] => none
  | .bob _ _ _, [] => none
  | .alice _ zero one, bit :: s => if bit then one.decode s else zero.decode s
  | .bob _ zero one, bit :: s => if bit then one.decode s else zero.decode s

/-- The output is determined by the tree (hence public seed) and transcript. -/
theorem decode_run (t : Tree A B) (a : A) (b : B) :
    t.decode (t.run a b).1 = some (t.run a b).2 := by
  induction t with
  | leaf output => rfl
  | alice message zero one ihz iho =>
      cases h : message a <;> simp [run, decode, h, ihz, iho]
  | bob message zero one ihz iho =>
      cases h : message b <;> simp [run, decode, h, ihz, iho]

/-- Every execution communicates at most the depth of the public tree. -/
theorem run_length_le_depth (t : Tree A B) (a : A) (b : B) :
    (t.run a b).1.length ≤ t.depth := by
  induction t with
  | leaf output => simp [run, depth]
  | alice message zero one ihz iho =>
      cases h : message a <;> simp [run, depth, h, ihz, iho]
  | bob message zero one ihz iho =>
      cases h : message b <;> simp [run, depth, h, ihz, iho]

/-- All leaf paths, whether reachable on an input or not. -/
def leafPaths : Tree A B → Finset (List Bool)
  | .leaf _ => {[]}
  | .alice _ zero one => zero.leafPaths.image (false :: ·) ∪ one.leafPaths.image (true :: ·)
  | .bob _ zero one => zero.leafPaths.image (false :: ·) ∪ one.leafPaths.image (true :: ·)

@[simp] theorem leafPaths_comap {A' B' : Type*} (t : Tree A B) (f : A' → A) (g : B' → B) :
    (t.comap f g).leafPaths = t.leafPaths := by
  induction t <;> simp_all [comap, leafPaths]

@[simp] theorem leafPaths_mapOutput (t : Tree A B) (f : Bool → Bool) :
    (t.mapOutput f).leafPaths = t.leafPaths := by
  induction t <;> simp_all [mapOutput, leafPaths]

/-- Executions always end at a leaf path. -/
theorem run_mem_leafPaths (t : Tree A B) (a : A) (b : B) :
    (t.run a b).1 ∈ t.leafPaths := by
  induction t with
  | leaf output => simp [run, leafPaths]
  | alice message zero one ihz iho =>
      cases h : message a <;> simp [run, leafPaths, h, ihz, iho]
  | bob message zero one ihz iho =>
      cases h : message b <;> simp [run, leafPaths, h, ihz, iho]

private theorem branch_card_le (s t : Finset (List Bool)) (d e : ℕ)
    (hs : s.card ≤ 2 ^ d) (ht : t.card ≤ 2 ^ e) :
    (s.image (false :: ·) ∪ t.image (true :: ·)).card ≤ 2 ^ (max d e + 1) := by
  calc
    _ ≤ (s.image (false :: ·)).card + (t.image (true :: ·)).card := Finset.card_union_le _ _
    _ ≤ s.card + t.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ ≤ 2 ^ d + 2 ^ e := Nat.add_le_add hs ht
    _ ≤ 2 ^ max d e + 2 ^ max d e := Nat.add_le_add
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
    _ = _ := by simp [Nat.pow_succ, Nat.mul_two]

/-- A binary tree of depth `c` has at most `2^c` leaf transcripts.
This uses tree structure, not the set of all strings of length at most `c`. -/
theorem card_leafPaths_le (t : Tree A B) : t.leafPaths.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf output => simp [leafPaths, depth]
  | alice message zero one ihz iho => exact branch_card_le _ _ _ _ ihz iho
  | bob message zero one ihz iho => exact branch_card_le _ _ _ _ ihz iho

/-- Alice's consistency checks along a publicly specified transcript. -/
def AliceConsistent : Tree A B → A → List Bool → Prop
  | .leaf _, _, s => s = []
  | .alice _ _ _, _, [] => False
  | .bob _ _ _, _, [] => False
  | .alice message zero one, a, bit :: s =>
      message a = bit ∧ if bit then one.AliceConsistent a s else zero.AliceConsistent a s
  | .bob _ zero one, a, bit :: s =>
      if bit then one.AliceConsistent a s else zero.AliceConsistent a s

/-- Bob's consistency checks along a publicly specified transcript. -/
def BobConsistent : Tree A B → B → List Bool → Prop
  | .leaf _, _, s => s = []
  | .alice _ _ _, _, [] => False
  | .bob _ _ _, _, [] => False
  | .alice _ zero one, b, bit :: s =>
      if bit then one.BobConsistent b s else zero.BobConsistent b s
  | .bob message zero one, b, bit :: s =>
      message b = bit ∧ if bit then one.BobConsistent b s else zero.BobConsistent b s

/-- The fiber of a transcript is a rectangle in the players' augmented inputs. -/
theorem run_transcript_eq_iff (t : Tree A B) (a : A) (b : B) (s : List Bool) :
    (t.run a b).1 = s ↔ t.AliceConsistent a s ∧ t.BobConsistent b s := by
  induction t generalizing s with
  | leaf output => simp [run, AliceConsistent, BobConsistent, eq_comm]
  | alice message zero one ihz iho =>
      cases s with
      | nil => cases h : message a <;> simp [run, AliceConsistent, BobConsistent, h]
      | cons bit s =>
          cases bit <;> cases h : message a <;>
            simp [run, AliceConsistent, BobConsistent, h, ihz, iho]
  | bob message zero one ihz iho =>
      cases s with
      | nil => cases h : message b <;> simp [run, AliceConsistent, BobConsistent, h]
      | cons bit s =>
          cases bit <;> cases h : message b <;>
            simp [run, AliceConsistent, BobConsistent, h, ihz, iho]

/-- Standard deterministic rectangle/crossing formulation. -/
theorem transcript_cross (t : Tree A B) (a a' : A) (b b' : B) (s : List Bool)
    (h : (t.run a b).1 = s) (h' : (t.run a' b').1 = s) :
    (t.run a b').1 = s ∧ (t.run a' b).1 = s := by
  rw [run_transcript_eq_iff] at h h' ⊢
  exact ⟨⟨h.1, h'.2⟩, (run_transcript_eq_iff _ _ _ _).mpr ⟨h'.1, h.2⟩⟩

end Disjointness.Tree
