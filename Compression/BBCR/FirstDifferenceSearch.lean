module

public import BBCR.FirstDifferenceStep

/-! The finite communication-tree compiler for the backtracking search. The
public decoder reconstructs every search state from the actual messages. -/

@[expose] public section

open Disjointness
open scoped Classical

namespace BBCR.FirstDifference

open NoisySearch

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

noncomputable local instance (L : ℕ) : DecidableEq (String L) := Classical.decEq _

def advance (N : ℕ) (s : BoundedHistory.State N) (ans : Bool × Bool) : BoundedHistory.State N :=
  if hs : (walk ans s.1).length ≤ N then ⟨walk ans s.1,hs⟩ else s

theorem advance_length (N : ℕ) (s : BoundedHistory.State N) (ans : Bool × Bool) :
    (advance N s ans).1.length ≤ s.1.length + 1 := by
  unfold advance
  split_ifs
  · exact walk_length ans s.1
  · omega

theorem advance_active (N : ℕ) (s : BoundedHistory.State N) (ans : Bool × Bool) (hs : s.1.length < N) :
    (advance N s ans).1 = walk ans s.1 := by
  have hh : (walk ans s.1).length ≤ N := (walk_length ans s.1).trans (by omega)
  simp only [advance,dite_eq_left hh]

noncomputable def family (L t N : ℕ) (s : BoundedHistory.State N) := step L t s.1

def update (L N : ℕ) (s : BoundedHistory.State N) (_ : String L → Fin 16) (bits : List Bool) : BoundedHistory.State N :=
  advance N s (answers bits)

noncomputable def search (L t n : ℕ) :=
  ProtocolIteration.boundedProtocol (family L t n) (fun _ ↦ false) (update L n) n (22 * n) (BoundedHistory.root n)

theorem search_cost (L t n : ℕ) : (search L t n).cost ≤ 22 * n :=
  ProtocolIteration.bounded_cost _ _ _ _ _ _

theorem execute_length (L t N n : ℕ)
    (rp : ProtocolIteration.Plan (BoundedHistory.State N) n (String L → Fin 16))
    (ap bp : ProtocolIteration.Plan (BoundedHistory.State N) n Unit)
    (s : BoundedHistory.State N) (a b : String L) :
    (ProtocolIteration.execute (family L t N) (fun _ ↦ false) (update L N) n rp ap bp s a b).1.length = 22 * n := by
  induction n generalizing s with
  | zero => simp [ProtocolIteration.execute]
  | succ n ih =>
    have ha : ap 0 s = () := Subsingleton.elim _ _
    have hb : bp 0 s = () := Subsingleton.elim _ _
    simp only [ProtocolIteration.execute,Bool.false_eq_true,ite_false,List.length_append]
    have hlen := step_length L t s.1 (rp 0 s) a b
    change (((step L t s.1).tree (rp 0 s)).run (a,ap 0 s) (b,bp 0 s)).1.length + _ = _
    rw [ha,hb,hlen,ih]
    omega

noncomputable def decode (L t n : ℕ)
    (rp : ProtocolIteration.Plan (BoundedHistory.State n) n (String L → Fin 16)) (bits : List Bool) : BoundedHistory.State n :=
  (ProtocolIteration.decode (family L t n) (fun _ ↦ false) (update L n) n rp (BoundedHistory.root n) bits).getD (BoundedHistory.root n)

theorem decode_run (L t n : ℕ)
    (rp : ProtocolIteration.Plan (BoundedHistory.State n) n (String L → Fin 16))
    (ap bp : ProtocolIteration.Plan (BoundedHistory.State n) n Unit) (a b : String L) :
    decode L t n rp (((search L t n).tree rp).run (a,ap) (b,bp)).1 =
      (ProtocolIteration.execute (family L t n) (fun _ ↦ false) (update L n) n rp ap bp (BoundedHistory.root n) a b).2 := by
  have hlen := execute_length L t n n rp ap bp (BoundedHistory.root n) a b
  have hc : (((search L t n).tree rp).run (a,ap) (b,bp)).1 =
      (ProtocolIteration.execute (family L t n) (fun _ ↦ false) (update L n) n rp ap bp (BoundedHistory.root n) a b).1 := by
    change ((TreeTrace.cut (22 * n) (ProtocolIteration.tree (family L t n) (fun _ ↦ false)
      (update L n) n rp (BoundedHistory.root n))).run (a,ap) (b,bp)).1 = _
    rw [TreeTrace.cut_trace,ProtocolIteration.tree_run,List.take_of_length_le hlen.le]
  rw [hc,decode,ProtocolIteration.decode_run]
  rfl

theorem execute_state (L t n : ℕ)
    (rp : ProtocolIteration.Plan (BoundedHistory.State n) n (String L → Fin 16))
    (ap bp : ProtocolIteration.Plan (BoundedHistory.State n) n Unit) (a b : String L) :
    decode L t n rp (((search L t n).tree rp).run (a,ap) (b,bp)).1 =
      FiniteDynamics.stateAfter (ProtocolIteration.rowNext (family L t n) (fun _ ↦ false) (update L n) a b)
        n (BoundedHistory.root n) (ProtocolIteration.regroup n (rp,ap,bp)) := by
  rw [decode_run,ProtocolIteration.execute_state]

end BBCR.FirstDifference
