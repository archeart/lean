module

public import BBCR.IndexedRejection

/-! The common public leaf index needs no binary encoding. Two flags decide
whether either local cutoff precedes it; indices are sent only in that case. -/

@[expose] public section

open Disjointness
open scoped Classical

namespace BBCR.LazyIndexExchange

variable {A B : Type*}

def flags (a : A → Bool) (b : B → Bool) (k : Bool → Bool → Tree A B) : Tree A B :=
  .alice a (.bob b (k false false) (k false true)) (.bob b (k true false) (k true true))

theorem flags_run (a : A → Bool) (b : B → Bool) (k : Bool → Bool → Tree A B) (x : A) (y : B) :
    (flags a b k).run x y = ([a x,b y] ++ ((k (a x) (b y)).run x y).1, ((k (a x) (b y)).run x y).2) := by
  cases ha : a x <;> cases hb : b y <;> simp [flags, Tree.run, ha, hb]

theorem flags_depth (a : A → Bool) (b : B → Bool) (k : Bool → Bool → Tree A B)
    (d : ℕ) (hk : ∀ i j, (k i j).depth ≤ d) : (flags a b k).depth ≤ 2 + d := by
  simp only [flags, Tree.depth]
  have h₀₀ := hk false false
  have h₀₁ := hk false true
  have h₁₀ := hk true false
  have h₁₁ := hk true true
  omega

noncomputable def exchange (C : ℕ) (default : Fin (C + 1))
    (a : A → Fin (C + 1)) (b : B → Fin (C + 1))
    (k : Fin (C + 1) → Fin (C + 1) → Tree A B) : Tree A B :=
  flags (fun x ↦ decide (a x ≠ default)) (fun y ↦ decide (b y ≠ default)) (fun fa fb ↦
    if fa || fb then FrontierLocation.exchange C a b k else k default default)

def prefixBits (C : ℕ) (default i j : Fin (C + 1)) : List Bool :=
  [decide (i ≠ default), decide (j ≠ default)] ++
    if i = default ∧ j = default then [] else
      List.ofFn (FrontierLocation.encode C i) ++ List.ofFn (FrontierLocation.encode C j)

theorem exchange_run (C : ℕ) (default : Fin (C + 1))
    (a : A → Fin (C + 1)) (b : B → Fin (C + 1))
    (k : Fin (C + 1) → Fin (C + 1) → Tree A B) (x : A) (y : B) :
    (exchange C default a b k).run x y =
      (prefixBits C default (a x) (b y) ++ ((k (a x) (b y)).run x y).1,
        ((k (a x) (b y)).run x y).2) := by
  by_cases ha : a x = default <;> by_cases hb : b y = default <;>
    simp [exchange, flags_run, ha, hb, prefixBits, FrontierLocation.exchange_run, List.append_assoc]

theorem exchange_depth (C : ℕ) (default : Fin (C + 1))
    (a : A → Fin (C + 1)) (b : B → Fin (C + 1))
    (k : Fin (C + 1) → Fin (C + 1) → Tree A B) (d : ℕ)
    (hk : ∀ i j, (k i j).depth ≤ d) :
    (exchange C default a b k).depth ≤ 2 + 2 * FrontierLocation.width C + d := by
  apply (flags_depth _ _ _ (2 * FrontierLocation.width C + d) ?_).trans (by omega)
  intro fa fb
  split_ifs
  · exact FrontierLocation.exchange_depth C a b k d hk
  · exact (hk default default).trans (by omega)

theorem prefixBits_length (C : ℕ) (default i j : Fin (C + 1)) :
    (prefixBits C default i j).length = 2 +
      if i = default ∧ j = default then 0 else 2 * FrontierLocation.width C := by
  by_cases hh : i = default ∧ j = default
  · simp [prefixBits, hh]
  · simp only [prefixBits, hh, ite_false, List.length_append, List.length_cons,
      List.length_nil, List.length_ofFn]
    omega

end BBCR.LazyIndexExchange

namespace BBCR.LazyIndexedRejection

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] {C : ℕ}

noncomputable def protocol (d : IndexedRejection.Data X Y Z C) (default : Z → Fin (C + 1)) :
    Protocol X Y Z (IndexedRejection.Tape X Z C) (IndexedRejection.Tape Y Z C) where
  publicLaw := d.proposal
  aliceLaw := IndexedRejection.aliceTable d
  bobLaw := IndexedRejection.bobTable d
  tree z := LazyIndexExchange.exchange C (default z) (fun xt ↦ d.aliceIndex z xt.1) (fun yt ↦ d.bobIndex z yt.1)
    (fun i j ↦ LocalRejection.tree (fun xt ↦ xt.2 (xt.1,z,min i j)) (fun yt ↦ yt.2 (yt.1,z,min i j)))

noncomputable def decode (default : Z → Fin (C + 1)) (v : Z × List Bool) : Option (Z × Fin (C + 1)) :=
  if v.2.getD 0 false || v.2.getD 1 false then IndexedRejection.decode C (v.1,v.2.drop 2)
  else (LocalRejection.decode (v.1,v.2.drop 2)).map (fun z ↦ (z,default z))

omit [Fintype Z] in
theorem decode_encoded (default : Z → Fin (C + 1)) (z : Z) (i j : Fin (C + 1)) (a b : Bool) :
    decode default (z, LazyIndexExchange.prefixBits C (default z) i j ++ [a,b]) =
      if a && b then some (z,min i j) else none := by
  by_cases hi : i = default z <;> by_cases hj : j = default z
  all_goals simp [decode, LazyIndexExchange.prefixBits, hi, hj, LocalRejection.decode, List.append_assoc]
  all_goals rw [← List.append_assoc, IndexedRejection.decode_encoded]
  all_goals simp only [Bool.and_eq_true]

theorem decoded_run (d : IndexedRejection.Data X Y Z C) (default : Z → Fin (C + 1))
    (z : Z) (x : X) (y : Y) (ta : IndexedRejection.Tape X Z C) (tb : IndexedRejection.Tape Y Z C) :
    decode default (z, (((protocol d default).tree z).run (x,ta) (y,tb)).1) =
      if ta (x,z,IndexedRejection.index d z x y) && tb (y,z,IndexedRejection.index d z x y)
        then some (z,IndexedRejection.index d z x y) else none := by
  simp only [protocol, LazyIndexExchange.exchange_run, LocalRejection.tree_run, IndexedRejection.index]
  exact decode_encoded _ _ _ _ _ _

theorem run_length (d : IndexedRejection.Data X Y Z C) (default : Z → Fin (C + 1))
    (z : Z) (x : X) (y : Y) (ta : IndexedRejection.Tape X Z C) (tb : IndexedRejection.Tape Y Z C) :
    ((((protocol d default).tree z).run (x,ta) (y,tb)).1).length = 4 +
      if d.aliceIndex z x = default z ∧ d.bobIndex z y = default z then 0 else 2 * FrontierLocation.width C := by
  simp only [protocol, LazyIndexExchange.exchange_run, LocalRejection.tree_run, List.length_append,
    LazyIndexExchange.prefixBits_length]
  simp only [List.length_cons, List.length_nil]
  split_ifs <;> omega

theorem cost_le (d : IndexedRejection.Data X Y Z C) (default : Z → Fin (C + 1)) :
    (protocol d default).cost ≤ 4 + 2 * FrontierLocation.width C := by
  apply Finset.sup_le
  intro z _
  dsimp only [protocol]
  exact (LazyIndexExchange.exchange_depth _ _ _ _ _ 2 (fun _ _ ↦ le_rfl)).trans (by omega)

theorem decoded_law (d : IndexedRejection.Data X Y Z C) (default : Z → Fin (C + 1)) (x : X) (y : Y) :
    ((protocol d default).viewLaw x y).map (decode default) =
      ((IndexedRejection.protocol d).viewLaw x y).map (IndexedRejection.decode C) := by
  simp only [Protocol.viewLaw, PMF.map_comp, Function.comp_def]
  change ((IndexedRejection.protocol d).seedLaw).map _ = ((IndexedRejection.protocol d).seedLaw).map _
  congr 1
  funext seeds
  rw [decoded_run, IndexedRejection.decoded_run]

end BBCR.LazyIndexedRejection
