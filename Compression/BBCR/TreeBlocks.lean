module

public import Disjointness.Tree

/-! Sending a whole fixed-length local block, followed by a public continuation.
These are actual binary communication trees, with proved execution and cost. -/

@[expose] public section

open Disjointness

namespace BBCR.TreeBlocks

variable {A B : Type*}

def alice : (n : ℕ) → (A → Fin n → Bool) → ((Fin n → Bool) → Tree A B) → Tree A B
  | 0, _, k => k Fin.elim0
  | n + 1, q, k => .alice (fun a ↦ q a 0)
      (alice n (fun a i ↦ q a i.succ) (fun v ↦ k (Fin.cons false v)))
      (alice n (fun a i ↦ q a i.succ) (fun v ↦ k (Fin.cons true v)))

def bob : (n : ℕ) → (B → Fin n → Bool) → ((Fin n → Bool) → Tree A B) → Tree A B
  | 0, _, k => k Fin.elim0
  | n + 1, q, k => .bob (fun b ↦ q b 0)
      (bob n (fun b i ↦ q b i.succ) (fun v ↦ k (Fin.cons false v)))
      (bob n (fun b i ↦ q b i.succ) (fun v ↦ k (Fin.cons true v)))

theorem run_alice (n : ℕ) (q : A → Fin n → Bool) (k : (Fin n → Bool) → Tree A B) (a : A) (b : B) :
    (alice n q k).run a b =
      (List.ofFn (q a) ++ ((k (q a)).run a b).1, ((k (q a)).run a b).2) := by
  induction n with
  | zero =>
    have hq : q a = Fin.elim0 := Subsingleton.elim _ _
    simp [alice, hq]
  | succ n ih =>
    cases h : q a 0 <;>
      have he := Fin.cons_self_tail (q a)
    all_goals simp only [h] at he
    all_goals change Fin.cons _ (fun i ↦ q a i.succ) = q a at he
    all_goals simp [alice, Tree.run, h, ih, List.ofFn_succ, he]

theorem run_bob (n : ℕ) (q : B → Fin n → Bool) (k : (Fin n → Bool) → Tree A B) (a : A) (b : B) :
    (bob n q k).run a b =
      (List.ofFn (q b) ++ ((k (q b)).run a b).1, ((k (q b)).run a b).2) := by
  induction n with
  | zero =>
    have hq : q b = Fin.elim0 := Subsingleton.elim _ _
    simp [bob, hq]
  | succ n ih =>
    cases h : q b 0 <;>
      have he := Fin.cons_self_tail (q b)
    all_goals simp only [h] at he
    all_goals change Fin.cons _ (fun i ↦ q b i.succ) = q b at he
    all_goals simp [bob, Tree.run, h, ih, List.ofFn_succ, he]

theorem depth_alice_le (n : ℕ) (q : A → Fin n → Bool) (k : (Fin n → Bool) → Tree A B)
    (d : ℕ) (hk : ∀ v, (k v).depth ≤ d) : (alice n q k).depth ≤ n + d := by
  induction n with
  | zero => simpa [alice] using hk Fin.elim0
  | succ n ih =>
    have hz := ih (fun a i ↦ q a i.succ) (fun v ↦ k (Fin.cons false v)) (fun v ↦ hk _)
    have ho := ih (fun a i ↦ q a i.succ) (fun v ↦ k (Fin.cons true v)) (fun v ↦ hk _)
    simp only [alice, Tree.depth]
    omega

theorem depth_bob_le (n : ℕ) (q : B → Fin n → Bool) (k : (Fin n → Bool) → Tree A B)
    (d : ℕ) (hk : ∀ v, (k v).depth ≤ d) : (bob n q k).depth ≤ n + d := by
  induction n with
  | zero => simpa [bob] using hk Fin.elim0
  | succ n ih =>
    have hz := ih (fun b i ↦ q b i.succ) (fun v ↦ k (Fin.cons false v)) (fun v ↦ hk _)
    have ho := ih (fun b i ↦ q b i.succ) (fun v ↦ k (Fin.cons true v)) (fun v ↦ hk _)
    simp only [bob, Tree.depth]
    omega

end BBCR.TreeBlocks
