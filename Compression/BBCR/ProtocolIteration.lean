module

public import BBCR.FiniteDynamics
public import BBCR.NoiseResampling

/-! Actual finite communication trees for iterating a public-state protocol.
Independent finite tables supply fresh seeds at every time and state. -/

@[expose] public section

open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR.BoundedHistory

abbrev State (C : ℕ) := {s : List Bool // s.length ≤ C}

def encode (C : ℕ) (s : State C) : Fin (C + 1) × (Fin C → Bool) :=
  (⟨s.1.length, by omega⟩, fun i ↦ s.1.getD i.val false)

theorem encode_injective (C : ℕ) : Function.Injective (encode C) := by
  intro s t h
  apply Subtype.ext
  have hlen : s.1.length = t.1.length := congrArg (fun z ↦ z.1.val) h
  apply List.ext_getElem hlen
  intro i hi hj
  have he := congrFun (congrArg Prod.snd h) ⟨i,hi.trans_le s.2⟩
  simpa only [encode, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] using he

noncomputable instance (C : ℕ) : Fintype (State C) := Fintype.ofInjective (encode C) (encode_injective C)

def root (C : ℕ) : State C := ⟨[],by simp⟩

end BBCR.BoundedHistory

namespace BBCR.TreeTrace

variable {A B : Type*}

def bind : Tree A B → (List Bool → Bool → Tree A B) → Tree A B
  | .leaf o, k => k [] o
  | .alice q z o, k => .alice q (bind z (fun s b ↦ k (false :: s) b)) (bind o (fun s b ↦ k (true :: s) b))
  | .bob q z o, k => .bob q (bind z (fun s b ↦ k (false :: s) b)) (bind o (fun s b ↦ k (true :: s) b))

theorem bind_run (t : Tree A B) (k : List Bool → Bool → Tree A B) (a : A) (b : B) :
    (bind t k).run a b =
      ((t.run a b).1 ++ ((k (t.run a b).1 (t.run a b).2).run a b).1,
        ((k (t.run a b).1 (t.run a b).2).run a b).2) := by
  induction t generalizing k with
  | leaf o => simp [bind, Tree.run]
  | alice q z o hz ho => cases h : q a <;> simp [bind, Tree.run, h, hz, ho]
  | bob q z o hz ho => cases h : q b <;> simp [bind, Tree.run, h, hz, ho]

def parse : Tree A B → List Bool → Option (List Bool × (List Bool × Bool))
  | .leaf o, bits => some ([],bits,o)
  | .alice _ _ _, [] => none
  | .bob _ _ _, [] => none
  | .alice _ z o, bit :: bits => (parse (if bit then o else z) bits).map (fun w ↦ (bit :: w.1,w.2))
  | .bob _ z o, bit :: bits => (parse (if bit then o else z) bits).map (fun w ↦ (bit :: w.1,w.2))

theorem parse_run_append (t : Tree A B) (a : A) (b : B) (rest : List Bool) :
    parse t ((t.run a b).1 ++ rest) = some ((t.run a b).1,rest,(t.run a b).2) := by
  induction t with
  | leaf o => simp [parse, Tree.run]
  | alice q z o hz ho => cases h : q a <;> simp [parse, Tree.run, h, hz, ho]
  | bob q z o hz ho => cases h : q b <;> simp [parse, Tree.run, h, hz, ho]

def cut : ℕ → Tree A B → Tree A B
  | _, .leaf o => .leaf o
  | 0, .alice _ _ _ => .leaf false
  | 0, .bob _ _ _ => .leaf false
  | n + 1, .alice q z o => .alice q (cut n z) (cut n o)
  | n + 1, .bob q z o => .bob q (cut n z) (cut n o)

theorem cut_depth (n : ℕ) (t : Tree A B) : (cut n t).depth ≤ n := by
  induction n generalizing t with
  | zero => cases t <;> rfl
  | succ n ih =>
    cases t with
    | leaf o => simp [cut, Tree.depth]
    | alice q z o =>
      simp only [cut, Tree.depth]
      have hz := ih z
      have ho := ih o
      omega
    | bob q z o =>
      simp only [cut, Tree.depth]
      have hz := ih z
      have ho := ih o
      omega

theorem cut_trace (n : ℕ) (t : Tree A B) (a : A) (b : B) :
    ((cut n t).run a b).1 = (t.run a b).1.take n := by
  induction n generalizing t with
  | zero => cases t <;> rfl
  | succ n ih => cases t with
    | leaf o => rfl
    | alice q z o => cases h : q a <;> simp [cut, Tree.run, h, ih]
    | bob q z o => cases h : q b <;> simp [cut, Tree.run, h, ih]

end BBCR.TreeTrace

namespace BBCR.ProtocolIteration

variable {X Y S R SA SB : Type*}

abbrev Plan (S : Type*) (n : ℕ) (A : Type*) := Fin n → S → A

noncomputable def tree (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) : (n : ℕ) → Plan S n R → S → Tree (X × Plan S n SA) (Y × Plan S n SB)
  | 0, _, _ => .leaf false
  | n + 1, rp, s => if terminal s then .leaf false else
      TreeTrace.bind (((p s).tree (rp 0 s)).comap (fun a ↦ (a.1,a.2 0 s)) (fun b ↦ (b.1,b.2 0 s)))
        (fun bits _ ↦ (tree p terminal update n (Fin.tail rp) (update s (rp 0 s) bits)).comap
          (fun a ↦ (a.1,Fin.tail a.2)) (fun b ↦ (b.1,Fin.tail b.2)))

def execute (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) :
    (n : ℕ) → Plan S n R → Plan S n SA → Plan S n SB → S → X → Y → List Bool × S
  | 0, _, _, _, s, _, _ => ([],s)
  | n + 1, rp, ap, bp, s, x, y => if terminal s then ([],s) else
      let head := (((p s).tree (rp 0 s)).run (x,ap 0 s) (y,bp 0 s)).1
      let tail := execute p terminal update n (Fin.tail rp) (Fin.tail ap) (Fin.tail bp) (update s (rp 0 s) head) x y
      (head ++ tail.1,tail.2)

theorem tree_run (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) (n : ℕ) (rp : Plan S n R) (ap : Plan S n SA) (bp : Plan S n SB)
    (s : S) (x : X) (y : Y) :
    ((tree p terminal update n rp s).run (x,ap) (y,bp)).1 = (execute p terminal update n rp ap bp s x y).1 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hs : terminal s with
    | true => simp [tree, execute, hs, Tree.run]
    | false => simp [tree, execute, hs, TreeTrace.bind_run, Disjointness.Tree.run_comap, ih]

def decode (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) : (n : ℕ) → Plan S n R → S → List Bool → Option S
  | 0, _, s, _ => some s
  | n + 1, rp, s, bits => if terminal s then some s else
      (TreeTrace.parse ((p s).tree (rp 0 s)) bits).bind (fun head ↦
        decode p terminal update n (Fin.tail rp) (update s (rp 0 s) head.1) head.2.1)

theorem decode_run (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) (n : ℕ) (rp : Plan S n R) (ap : Plan S n SA) (bp : Plan S n SB)
    (s : S) (x : X) (y : Y) :
    decode p terminal update n rp s (execute p terminal update n rp ap bp s x y).1 =
      some (execute p terminal update n rp ap bp s x y).2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hs : terminal s with
    | true => simp [decode, execute, hs]
    | false =>
      simp only [decode, execute, hs, Bool.false_eq_true, ite_false]
      rw [TreeTrace.parse_run_append]
      simp only [Option.bind_some]
      exact ih _ _ _ _

variable [Fintype S] [Fintype R] [Fintype SA] [Fintype SB]

noncomputable def protocol (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) (n : ℕ) (s : S) :
    Protocol X Y (Plan S n R) (Plan S n SA) (Plan S n SB) where
  publicLaw := pi (fun _ : Fin n ↦ pi (fun s ↦ (p s).publicLaw))
  aliceLaw := pi (fun _ : Fin n ↦ pi (fun s ↦ (p s).aliceLaw))
  bobLaw := pi (fun _ : Fin n ↦ pi (fun s ↦ (p s).bobLaw))
  tree rp := tree p terminal update n rp s

noncomputable def boundedProtocol (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) (n Q : ℕ) (s : S) :
    Protocol X Y (Plan S n R) (Plan S n SA) (Plan S n SB) where
  publicLaw := (protocol p terminal update n s).publicLaw
  aliceLaw := (protocol p terminal update n s).aliceLaw
  bobLaw := (protocol p terminal update n s).bobLaw
  tree rp := TreeTrace.cut Q (tree p terminal update n rp s)

theorem bounded_cost (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) (n Q : ℕ) (s : S) :
    (boundedProtocol p terminal update n Q s).cost ≤ Q := by
  apply Finset.sup_le
  intro rp _
  exact TreeTrace.cut_depth Q _

abbrev Rows (S R SA SB : Type*) := (S → R) × ((S → SA) × (S → SB))

def regroup (n : ℕ) : (Plan S n R × (Plan S n SA × Plan S n SB)) ≃ (Fin n → Rows S R SA SB) where
  toFun z i := (z.1 i,z.2.1 i,z.2.2 i)
  invFun z := ((fun i ↦ (z i).1),(fun i ↦ (z i).2.1),(fun i ↦ (z i).2.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def rowLaw (p : S → Protocol X Y R SA SB) : PMF (Rows S R SA SB) :=
  joint (pi (fun s ↦ (p s).publicLaw)) (fun _ ↦
    joint (pi (fun s ↦ (p s).aliceLaw)) (fun _ ↦ pi (fun s ↦ (p s).bobLaw)))

theorem regroup_law (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) (n : ℕ) (s : S) :
    ((protocol p terminal update n s).seedLaw).map (regroup n) = pi (fun _ : Fin n ↦ rowLaw p) := by
  have hrow (row : Rows S R SA SB) : rowLaw p row =
      (pi (fun t ↦ (p t).publicLaw)) row.1 *
        ((pi (fun t ↦ (p t).aliceLaw)) row.2.1 * (pi (fun t ↦ (p t).bobLaw)) row.2.2) := by
    rcases row with ⟨rp,ap,bp⟩
    rw [rowLaw, joint_apply, joint_apply]
  apply PMF.ext
  intro rows
  rw [map_equiv_apply]
  simp only [regroup, Equiv.coe_fn_symm_mk, Protocol.seedLaw_apply, protocol, pi_apply,
    hrow, Finset.prod_mul_distrib]

theorem pi_eval {I A : Type*} [Fintype I] [Fintype A] (q : I → PMF A) (i : I) :
    (pi q).map (fun row ↦ row i) = q i := by
  have hh := congrArg (fun law ↦ law.map Prod.fst) (pi_split q i)
  rw [joint_map_fst, PMF.map_comp] at hh
  exact hh

theorem row_select (p : S → Protocol X Y R SA SB) (s : S) :
    (rowLaw p).map (fun row ↦ (row.1 s,row.2.1 s,row.2.2 s)) = (p s).seedLaw := by
  have hr := pi_eval (fun t ↦ (p t).publicLaw) s
  have ha := pi_eval (fun t ↦ (p t).aliceLaw) s
  have hb := pi_eval (fun t ↦ (p t).bobLaw) s
  simp only [Protocol.seedLaw]
  rw [← hr, ← ha, ← hb]
  simp only [rowLaw, joint_eq_bind, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]

theorem expect_row_select (p : S → Protocol X Y R SA SB) (s : S) (g : R × (SA × SB) → ℝ) :
    FiniteAzuma.expect (rowLaw p) (fun row ↦ g (row.1 s,row.2.1 s,row.2.2 s)) =
      FiniteAzuma.expect (p s).seedLaw g := by
  rw [← FiniteAzuma.expect_map, row_select]

def rowNext (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) (x : X) (y : Y) (s : S) (row : Rows S R SA SB) : S :=
  if terminal s then s else update s (row.1 s) (((p s).tree (row.1 s)).run (x,row.2.1 s) (y,row.2.2 s)).1

def rowCost (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (x : X) (y : Y) (s : S) (row : Rows S R SA SB) : ℝ :=
  if terminal s then 0 else ((((p s).tree (row.1 s)).run (x,row.2.1 s) (y,row.2.2 s)).1.length : ℝ)

omit [Fintype S] [Fintype R] [Fintype SA] [Fintype SB] in
theorem execute_terminal (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) (n : ℕ) (rp : Plan S n R) (ap : Plan S n SA) (bp : Plan S n SB)
    (s : S) (hs : terminal s = true) (x : X) (y : Y) : execute p terminal update n rp ap bp s x y = ([],s) := by
  cases n <;> simp [execute, hs]

omit [Fintype S] [Fintype R] [Fintype SA] [Fintype SB] in
theorem execute_state (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) (n : ℕ) (rp : Plan S n R) (ap : Plan S n SA) (bp : Plan S n SB)
    (s : S) (x : X) (y : Y) :
    (execute p terminal update n rp ap bp s x y).2 =
      FiniteDynamics.stateAfter (rowNext p terminal update x y) n s (regroup n (rp,ap,bp)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hs : terminal s with
    | true =>
      rw [execute_terminal p terminal update _ _ _ _ s hs]
      exact (FiniteDynamics.state_after_terminal terminal (rowNext p terminal update x y)
        (fun t ht row ↦ by simp [rowNext,ht]) _ s hs _).symm
    | false =>
      simp only [execute, hs, Bool.false_eq_true, ite_false, FiniteDynamics.stateAfter, rowNext,
        regroup, Equiv.coe_fn_mk]
      exact ih _ _ _ _

omit [Fintype S] [Fintype R] [Fintype SA] [Fintype SB] in
theorem execute_length (p : S → Protocol X Y R SA SB) (terminal : S → Bool)
    (update : S → R → List Bool → S) (n : ℕ) (rp : Plan S n R) (ap : Plan S n SA) (bp : Plan S n SB)
    (s : S) (x : X) (y : Y) :
    ((execute p terminal update n rp ap bp s x y).1.length : ℝ) =
      FiniteDynamics.rewardTotal (rowNext p terminal update x y) (rowCost p terminal x y) n s (regroup n (rp,ap,bp)) := by
  induction n generalizing s with
  | zero => simp [execute, FiniteDynamics.rewardTotal]
  | succ n ih =>
    cases hs : terminal s with
    | true =>
      simp only [FiniteDynamics.rewardTotal, rowNext, rowCost, hs, ite_true]
      have he : Fin.tail (regroup (n + 1) (rp,ap,bp)) = regroup n (Fin.tail rp,Fin.tail ap,Fin.tail bp) := rfl
      rw [he, ← ih]
      simp [execute_terminal p terminal update _ _ _ _ s hs]
    | false =>
      simp only [execute, hs, Bool.false_eq_true, ite_false, FiniteDynamics.rewardTotal, rowNext, rowCost,
        regroup, Equiv.coe_fn_mk, List.length_append, Nat.cast_add]
      rw [ih]
      rfl

theorem dynamics_law (q : PMF (Rows S R SA SB)) (next : S → Rows S R SA SB → S)
    (f : S → Rows S R SA SB → ℝ) (n : ℕ) (s : S) :
    (FiniteDynamics.process q next f n s).law = pi (fun _ : Fin n ↦ q) := by
  have hh : (FiniteDynamics.process q next f n s).law =
      (FiniteAzuma.Process.iid q (fun _ ↦ 0) 0 0 n).law := by
    induction n generalizing s with
    | zero => rfl
    | succ n ih => simp only [FiniteDynamics.process, FiniteAzuma.Process.law, FiniteAzuma.Process.iid, ih]
  rw [hh, FiniteAzuma.Process.iid_law]

end BBCR.ProtocolIteration
