module

public import BBCR.FirstDifferenceOracle

/-! An actual public-coin backtracking-search step. Four fingerprints cost
twenty bits; two explicit public answer bits simplify the state decoder. -/

@[expose] public section

open Disjointness
open scoped Classical

namespace BBCR.FirstDifference

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

noncomputable local instance (L : ℕ) : DecidableEq (String L) := Classical.decEq _

theorem membershipTree_trace (L t : ℕ) (v : List Bool) (h : String L → Fin 16)
    (k : Bool → Tree (String L) (String L)) (a b : String L) :
    ∃ front : List Bool, front.length = 10 ∧
      (membershipTree L t v h k).run a b =
        (front ++ ((k (membership L t a b v h)).run a b).1,((k (membership L t a b v h)).run a b).2) := by
  let lo := decide (h (key L a (lower t v)) = h (key L b (lower t v)))
  let hi := decide (h (key L a (upper t v)) = h (key L b (upper t v)))
  refine ⟨List.ofFn (FrontierLocation.encode 15 (h (key L a (lower t v)))) ++ [lo] ++
    List.ofFn (FrontierLocation.encode 15 (h (key L a (upper t v)))) ++ [hi],?_,?_⟩
  · simp [FingerprintProtocol.width16]
  · simp only [membershipTree,FingerprintProtocol.run,lo,hi,membership,List.append_assoc,List.cons_append,List.nil_append]

theorem oracleTree_trace (L t : ℕ) (v : List Bool) (h : String L → Fin 16)
    (k : Bool × Bool → Tree (String L) (String L)) (a b : String L) :
    ∃ front : List Bool, front.length = 20 ∧
      (oracleTree L t v h k).run a b =
        (front ++ ((k (oracle L t a b v h)).run a b).1,((k (oracle L t a b v h)).run a b).2) := by
  obtain ⟨f,hf,he⟩ := membershipTree_trace L t v h
    (fun ans ↦ membershipTree L t (v ++ [false]) h (fun ans' ↦ k (ans,ans'))) a b
  obtain ⟨g,hg,hh⟩ := membershipTree_trace L t (v ++ [false]) h
    (fun ans ↦ k (membership L t a b v h,ans)) a b
  refine ⟨f ++ g,by simp [hf,hg],?_⟩
  simp only [oracleTree,he,hh,oracle,List.append_assoc]

def answerBits (ans : Bool × Bool) : Fin 2 → Bool := fun i ↦ if i.val = 0 then ans.1 else ans.2

theorem answerBits_list (ans : Bool × Bool) : List.ofFn (answerBits ans) = [ans.1,ans.2] := by
  simp [List.ofFn_succ,answerBits]

noncomputable def step (L t : ℕ) (v : List Bool) :
    Protocol (String L) (String L) (String L → Fin 16) Unit Unit where
  publicLaw := FiniteHashing.law (String L)
  aliceLaw := PMF.pure ()
  bobLaw := PMF.pure ()
  tree h := (oracleTree L t v h (fun ans ↦ TreeBlocks.alice 2 (fun _ ↦ answerBits ans) (fun _ ↦ .leaf false))).comap Prod.fst Prod.fst

theorem step_cost (L t : ℕ) (v : List Bool) : (step L t v).cost ≤ 22 := by
  apply Finset.sup_le
  intro h _
  rw [step,Tree.depth_comap]
  exact (oracleTree_depth L t v h _ 2 (fun ans ↦
    TreeBlocks.depth_alice_le 2 (fun _ ↦ answerBits ans) (fun _ ↦ .leaf false) 0 (fun _ ↦ le_rfl))).trans_eq (by omega)

def answers (bits : List Bool) : Bool × Bool := (bits.getD 20 false,bits.getD 21 false)

theorem step_run (L t : ℕ) (v : List Bool) (h : String L → Fin 16) (a b : String L) :
    ∃ front : List Bool, front.length = 20 ∧
      (((step L t v).tree h).run (a,()) (b,())).1 = front ++ [((oracle L t a b v h).1),((oracle L t a b v h).2)] := by
  obtain ⟨front,hf,he⟩ := oracleTree_trace L t v h
    (fun ans ↦ TreeBlocks.alice 2 (fun _ ↦ answerBits ans) (fun _ ↦ .leaf false)) a b
  refine ⟨front,hf,?_⟩
  simp only [step,Tree.run_comap,he,TreeBlocks.run_alice,Tree.run,List.append_nil,answerBits_list]

theorem step_length (L t : ℕ) (v : List Bool) (h : String L → Fin 16) (a b : String L) :
    (((step L t v).tree h).run (a,()) (b,())).1.length = 22 := by
  obtain ⟨front,hf,he⟩ := step_run L t v h a b
  rw [he]
  simp [hf]

theorem step_answers (L t : ℕ) (v : List Bool) (h : String L → Fin 16) (a b : String L) :
    answers (((step L t v).tree h).run (a,()) (b,())).1 = oracle L t a b v h := by
  obtain ⟨front,hf,he⟩ := step_run L t v h a b
  rw [he]
  have h₁ : (front ++ [(oracle L t a b v h).1,(oracle L t a b v h).2]).getD front.length false = (oracle L t a b v h).1 := by simp
  have h₂ : (front ++ [(oracle L t a b v h).1,(oracle L t a b v h).2]).getD (front.length + 1) false = (oracle L t a b v h).2 := by simp
  rw [hf] at h₁ h₂
  exact Prod.ext h₁ h₂

end BBCR.FirstDifference
