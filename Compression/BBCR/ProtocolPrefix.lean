module

public import Disjointness.Factorization
public import Disjointness.Hellinger

/-! Prefix events and their private-randomness factorization, proved from
the execution of the existing communication trees. -/

@[expose] public section

open Disjointness
open scoped ENNReal

namespace BBCR.Prefix

inductive Speaker where
  | alice
  | bob
  deriving DecidableEq

namespace Tree

variable {A B : Type*}

/-- The next speaker is public: it depends only on the tree and prefix. `none`
means that the prefix ends at a leaf or does not describe a tree node. -/
def speaker : Disjointness.Tree A B → List Bool → Option Speaker
  | .leaf _, _ => none
  | .alice _ _ _, [] => some .alice
  | .bob _ _ _, [] => some .bob
  | .alice _ z o, bit :: s => if bit then speaker o s else speaker z s
  | .bob _ z o, bit :: s => if bit then speaker o s else speaker z s

def AliceConsistent : Disjointness.Tree A B → A → List Bool → Prop
  | _, _, [] => True
  | .leaf _, _, _ :: _ => False
  | .alice q z o, a, bit :: s => q a = bit ∧ if bit then AliceConsistent o a s else AliceConsistent z a s
  | .bob _ z o, a, bit :: s => if bit then AliceConsistent o a s else AliceConsistent z a s

def BobConsistent : Disjointness.Tree A B → B → List Bool → Prop
  | _, _, [] => True
  | .leaf _, _, _ :: _ => False
  | .alice _ z o, b, bit :: s => if bit then BobConsistent o b s else BobConsistent z b s
  | .bob q z o, b, bit :: s => q b = bit ∧ if bit then BobConsistent o b s else BobConsistent z b s

def aliceDecision : Disjointness.Tree A B → A → List Bool → Bool
  | .leaf _, _, _ => false
  | .alice q _ _, a, [] => q a
  | .bob _ _ _, _, [] => false
  | .alice _ z o, a, bit :: s => if bit then aliceDecision o a s else aliceDecision z a s
  | .bob _ z o, a, bit :: s => if bit then aliceDecision o a s else aliceDecision z a s

def bobDecision : Disjointness.Tree A B → B → List Bool → Bool
  | .leaf _, _, _ => false
  | .alice _ _ _, _, [] => false
  | .bob q _ _, b, [] => q b
  | .alice _ z o, b, bit :: s => if bit then bobDecision o b s else bobDecision z b s
  | .bob _ z o, b, bit :: s => if bit then bobDecision o b s else bobDecision z b s

/-- Prefix rectangles hold for the actual communicated execution path. -/
theorem run_prefix_iff (t : Disjointness.Tree A B) (a : A) (b : B) (s : List Bool) :
    s.IsPrefix (t.run a b).1 ↔ AliceConsistent t a s ∧ BobConsistent t b s := by
  induction t generalizing s with
  | leaf output => cases s <;> simp [Disjointness.Tree.run, AliceConsistent, BobConsistent]
  | alice q z o ihz iho =>
    cases s with
    | nil => simp [AliceConsistent, BobConsistent]
    | cons bit s =>
      cases bit <;> cases h : q a <;>
        simp [Disjointness.Tree.run, AliceConsistent, BobConsistent, h, ihz, iho]
  | bob q z o ihz iho =>
    cases s with
    | nil => simp [AliceConsistent, BobConsistent]
    | cons bit s =>
      cases bit <;> cases h : q b <;>
        simp [Disjointness.Tree.run, AliceConsistent, BobConsistent, h, ihz, iho]

/-- At a public internal node, extending the prefix by a bit is exactly the
event that the prefix was reached and the actual next transmitted bit equals it. -/
theorem run_extension_iff (t : Disjointness.Tree A B) (a : A) (b : B) (s : List Bool)
    (who : Speaker) (howner : speaker t s = some who) (bit : Bool) :
    (s ++ [bit]).IsPrefix (t.run a b).1 ↔
      s.IsPrefix (t.run a b).1 ∧ (t.run a b).1.getD s.length false = bit := by
  induction t generalizing s with
  | leaf o => simp [speaker] at howner
  | alice q z o hz ho =>
    cases s with
    | nil => cases hq : q a <;> cases bit <;> simp [Disjointness.Tree.run, hq]
    | cons c s =>
      cases c <;> cases hq : q a <;>
        simp_all [speaker, Disjointness.Tree.run]
  | bob q z o hz ho =>
    cases s with
    | nil => cases hq : q b <;> cases bit <;> simp [Disjointness.Tree.run, hq]
    | cons c s =>
      cases c <;> cases hq : q b <;>
        simp_all [speaker, Disjointness.Tree.run]

theorem alice_append_implies (t : Disjointness.Tree A B) (a : A) (s : List Bool) (bit : Bool) :
    AliceConsistent t a (s ++ [bit]) → AliceConsistent t a s := by
  induction t generalizing s with
  | leaf o => cases s <;> simp [AliceConsistent]
  | alice q z o hz ho =>
    cases s with
    | nil => simp [AliceConsistent]
    | cons b s => cases b <;> simp_all [AliceConsistent]
  | bob q z o hz ho =>
    cases s with
    | nil => simp [AliceConsistent]
    | cons b s => cases b <;> simp_all [AliceConsistent]

theorem bob_append_implies (t : Disjointness.Tree A B) (b : B) (s : List Bool) (bit : Bool) :
    BobConsistent t b (s ++ [bit]) → BobConsistent t b s := by
  induction t generalizing s with
  | leaf o => cases s <;> simp [BobConsistent]
  | alice q z o hz ho =>
    cases s with
    | nil => simp [BobConsistent]
    | cons c s => cases c <;> simp_all [BobConsistent]
  | bob q z o hz ho =>
    cases s with
    | nil => simp [BobConsistent]
    | cons c s => cases c <;> simp_all [BobConsistent]

/-- Alice sending a bit imposes no new condition on Bob's private seed. -/
theorem bob_unchanged_of_alice (t : Disjointness.Tree A B) (s : List Bool)
    (h : speaker t s = some .alice) (b : B) (bit : Bool) :
    BobConsistent t b (s ++ [bit]) ↔ BobConsistent t b s := by
  induction t generalizing s with
  | leaf o => simp [speaker] at h
  | alice q z o hz ho =>
    cases s with
    | nil => cases bit <;> simp [BobConsistent]
    | cons c s => cases c <;> simp_all [speaker, BobConsistent]
  | bob q z o hz ho =>
    cases s with
    | nil => simp [speaker] at h
    | cons c s => cases c <;> simp_all [speaker, BobConsistent]

theorem alice_unchanged_of_bob (t : Disjointness.Tree A B) (s : List Bool)
    (h : speaker t s = some .bob) (a : A) (bit : Bool) :
    AliceConsistent t a (s ++ [bit]) ↔ AliceConsistent t a s := by
  induction t generalizing s with
  | leaf o => simp [speaker] at h
  | alice q z o hz ho =>
    cases s with
    | nil => simp [speaker] at h
    | cons c s => cases c <;> simp_all [speaker, AliceConsistent]
  | bob q z o hz ho =>
    cases s with
    | nil => cases bit <;> simp [AliceConsistent]
    | cons c s => cases c <;> simp_all [speaker, AliceConsistent]

theorem alice_extension_iff (t : Disjointness.Tree A B) (s : List Bool)
    (h : speaker t s = some .alice) (a : A) (bit : Bool) :
    AliceConsistent t a (s ++ [bit]) ↔ AliceConsistent t a s ∧ aliceDecision t a s = bit := by
  induction t generalizing s with
  | leaf o => simp [speaker] at h
  | alice q z o hz ho =>
    cases s with
    | nil => cases bit <;> simp [AliceConsistent, aliceDecision]
    | cons c s => cases c <;> simp_all [speaker, AliceConsistent, aliceDecision, and_assoc]
  | bob q z o hz ho =>
    cases s with
    | nil => simp [speaker] at h
    | cons c s => cases c <;> simp_all [speaker, AliceConsistent, aliceDecision]

theorem bob_extension_iff (t : Disjointness.Tree A B) (s : List Bool)
    (h : speaker t s = some .bob) (b : B) (bit : Bool) :
    BobConsistent t b (s ++ [bit]) ↔ BobConsistent t b s ∧ bobDecision t b s = bit := by
  induction t generalizing s with
  | leaf o => simp [speaker] at h
  | alice q z o hz ho =>
    cases s with
    | nil => simp [speaker] at h
    | cons c s => cases c <;> simp_all [speaker, BobConsistent, bobDecision]
  | bob q z o hz ho =>
    cases s with
    | nil => cases bit <;> simp [BobConsistent, bobDecision]
    | cons c s => cases c <;> simp_all [speaker, BobConsistent, bobDecision, and_assoc]
end Tree

namespace Protocol

variable {X Y R SA SB : Type*} [Fintype SA] [Fintype SB]

/-- Actual fixed-public-seed prefix law, obtained by taking the first `k`
communicated bits of the original execution. -/
noncomputable def law (p : Disjointness.Protocol X Y R SA SB) (r : R) (x : X) (y : Y) (k : ℕ) :
    PMF (List Bool) := (p.privateTranscriptLaw r x y).map (List.take k)

open scoped Classical in
noncomputable def aliceFactor (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (x : X) : ℝ≥0∞ :=
  ∑ a, if Tree.AliceConsistent (p.tree r) (x,a) s then p.aliceLaw a else 0

open scoped Classical in
noncomputable def bobFactor (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (y : Y) : ℝ≥0∞ :=
  ∑ b, if Tree.BobConsistent (p.tree r) (y,b) s then p.bobLaw b else 0

/-- Factorization of prefix probabilities follows from the prefix rectangle
property and independent private seed laws; it is not a protocol assumption. -/
theorem law_factorization (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool) :
    law p r x y s.length s = aliceFactor p r s x * bobFactor p r s y := by
  classical
  simp only [law, Disjointness.Protocol.privateTranscriptLaw, PMF.map_bind, PMF.map_comp,
    Function.comp_def, aliceFactor, bobFactor, PMF.bind_apply, PMF.map_apply,
    tsum_fintype, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : s = (((p.tree r).run (x,a) (y,b)).1).take s.length ↔
      Tree.AliceConsistent (p.tree r) (x,a) s ∧ Tree.BobConsistent (p.tree r) (y,b) s := by
    rw [← List.prefix_iff_eq_take]
    exact Tree.run_prefix_iff _ _ _ _
  by_cases ha : Tree.AliceConsistent (p.tree r) (x,a) s <;>
    by_cases hb : Tree.BobConsistent (p.tree r) (y,b) s <;> simp [he, ha, hb]

omit [Fintype SB] in
theorem aliceFactor_append_le (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (s : List Bool) (bit : Bool) :
    aliceFactor p r (s ++ [bit]) x ≤ aliceFactor p r s x := by
  classical
  apply Finset.sum_le_sum
  intro a _
  split_ifs with h h'
  · rfl
  · exact False.elim (h' (Tree.alice_append_implies _ _ _ _ h))
  · positivity
  · rfl

omit [Fintype SA] in
theorem bobFactor_append_le (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (y : Y) (s : List Bool) (bit : Bool) :
    bobFactor p r (s ++ [bit]) y ≤ bobFactor p r s y := by
  classical
  apply Finset.sum_le_sum
  intro b _
  split_ifs with h h'
  · rfl
  · exact False.elim (h' (Tree.bob_append_implies _ _ _ _ h))
  · positivity
  · rfl

omit [Fintype SA] in
theorem bobFactor_unchanged_of_alice (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (s : List Bool) (h : Tree.speaker (p.tree r) s = some .alice) (y : Y) (bit : Bool) :
    bobFactor p r (s ++ [bit]) y = bobFactor p r s y := by
  classical
  unfold bobFactor
  apply Finset.sum_congr rfl
  intro b _
  rw [Tree.bob_unchanged_of_alice _ _ h]

omit [Fintype SB] in
theorem aliceFactor_unchanged_of_bob (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (s : List Bool) (h : Tree.speaker (p.tree r) s = some .bob) (x : X) (bit : Bool) :
    aliceFactor p r (s ++ [bit]) x = aliceFactor p r s x := by
  classical
  unfold aliceFactor
  apply Finset.sum_congr rfl
  intro a _
  rw [Tree.alice_unchanged_of_bob _ _ h]

omit [Fintype SB] in
theorem aliceFactor_split (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (s : List Bool) (h : Tree.speaker (p.tree r) s = some .alice) (x : X) :
    aliceFactor p r (s ++ [false]) x + aliceFactor p r (s ++ [true]) x = aliceFactor p r s x := by
  classical
  unfold aliceFactor
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [Tree.alice_extension_iff _ _ h, Tree.alice_extension_iff _ _ h]
  by_cases ha : Tree.AliceConsistent (p.tree r) (x,a) s <;>
    cases Tree.aliceDecision (p.tree r) (x,a) s <;> simp [ha]

omit [Fintype SA] in
theorem bobFactor_split (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (s : List Bool) (h : Tree.speaker (p.tree r) s = some .bob) (y : Y) :
    bobFactor p r (s ++ [false]) y + bobFactor p r (s ++ [true]) y = bobFactor p r s y := by
  classical
  unfold bobFactor
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [Tree.bob_extension_iff _ _ h, Tree.bob_extension_iff _ _ h]
  by_cases hb : Tree.BobConsistent (p.tree r) (y,b) s <;>
    cases Tree.bobDecision (p.tree r) (y,b) s <;> simp [hb]

end Protocol
end BBCR.Prefix
