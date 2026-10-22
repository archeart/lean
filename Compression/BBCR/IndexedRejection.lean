module

public import BBCR.LocalRejection
public import BBCR.FrontierLocation
public import BBCR.SmoothingTree

/-! One implementable proposal/acceptance round, including communication of
the input-dependent stopping index. The proposal law is input independent. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.IndexedRejection

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

structure Data (X Y Z : Type) (C : ℕ) where
  proposal : PMF Z
  aliceIndex : Z → X → Fin (C + 1)
  bobIndex : Z → Y → Fin (C + 1)
  aliceAccept : X → Z → Fin (C + 1) → ℝ
  bobAccept : Y → Z → Fin (C + 1) → ℝ
  alice_nonneg : ∀ x z i, 0 ≤ aliceAccept x z i
  alice_le_one : ∀ x z i, aliceAccept x z i ≤ 1
  bob_nonneg : ∀ y z i, 0 ≤ bobAccept y z i
  bob_le_one : ∀ y z i, bobAccept y z i ≤ 1

variable {C : ℕ}

abbrev Tape (X Z : Type) (C : ℕ) := (X × (Z × Fin (C + 1))) → Bool

noncomputable def aliceTable (d : Data X Y Z C) : PMF (Tape X Z C) :=
  LocalRejection.table (fun i ↦ d.aliceAccept i.1 i.2.1 i.2.2)
    (fun i ↦ d.alice_nonneg i.1 i.2.1 i.2.2) (fun i ↦ d.alice_le_one i.1 i.2.1 i.2.2)

noncomputable def bobTable (d : Data X Y Z C) : PMF (Tape Y Z C) :=
  LocalRejection.table (fun i ↦ d.bobAccept i.1 i.2.1 i.2.2)
    (fun i ↦ d.bob_nonneg i.1 i.2.1 i.2.2) (fun i ↦ d.bob_le_one i.1 i.2.1 i.2.2)

noncomputable def protocol (d : Data X Y Z C) : Protocol X Y Z (Tape X Z C) (Tape Y Z C) where
  publicLaw := d.proposal
  aliceLaw := aliceTable d
  bobLaw := bobTable d
  tree z := FrontierLocation.exchange C (fun xt ↦ d.aliceIndex z xt.1) (fun yt ↦ d.bobIndex z yt.1)
    (fun i j ↦ LocalRejection.tree (fun xt ↦ xt.2 (xt.1,z,min i j)) (fun yt ↦ yt.2 (yt.1,z,min i j)))

def index (d : Data X Y Z C) (z : Z) (x : X) (y : Y) : Fin (C + 1) :=
  min (d.aliceIndex z x) (d.bobIndex z y)

noncomputable def decode (C : ℕ) (v : Z × List Bool) : Option (Z × Fin (C + 1)) :=
  let l := FrontierLocation.width C
  let i := FrontierLocation.decode C (SmoothingTree.blockVector l v.2)
  let j := FrontierLocation.decode C (SmoothingTree.blockVector l (v.2.drop l))
  let tail := (v.2.drop l).drop l
  if tail.getD 0 false && tail.getD 1 false then some (v.1,min i j) else none

omit [Fintype Z] in
theorem decode_encoded (z : Z) (i j : Fin (C + 1)) (a b : Bool) :
    decode C (z, List.ofFn (FrontierLocation.encode C i) ++
      List.ofFn (FrontierLocation.encode C j) ++ [a,b]) =
      if a && b then some (z,min i j) else none := by
  simp [decode, List.append_assoc, SmoothingTree.blockVector_append]

theorem decoded_run (d : Data X Y Z C) (z : Z) (x : X) (y : Y)
    (ta : Tape X Z C) (tb : Tape Y Z C) :
    decode C (z, (((protocol d).tree z).run (x,ta) (y,tb)).1) =
      if ta (x,z,index d z x y) && tb (y,z,index d z x y) then some (z,index d z x y) else none := by
  simp only [protocol, FrontierLocation.exchange_run, LocalRejection.tree_run, index]
  exact decode_encoded _ _ _ _ _

theorem cost_le (d : Data X Y Z C) : (protocol d).cost ≤ 2 * FrontierLocation.width C + 2 := by
  apply Finset.sup_le
  intro z _
  dsimp only [protocol]
  apply FrontierLocation.exchange_depth
  intro i j
  exact le_rfl

/-- Exact output law of the actual communication tree. Both acceptance coins
are independent private coordinates even though the selected index depends on
both inputs and the proposal. -/
theorem decoded_law (d : Data X Y Z C) (x : X) (y : Y) :
    ((protocol d).viewLaw x y).map (decode C) = d.proposal.bind (fun z ↦
      let i := index d z x y
      (LocalRejection.coin (d.aliceAccept x z i) (d.alice_nonneg x z i) (d.alice_le_one x z i)).bind fun a ↦
        (LocalRejection.coin (d.bobAccept y z i) (d.bob_nonneg y z i) (d.bob_le_one y z i)).map fun b ↦
          if a && b then some (z,i) else none) := by
  have he (z : Z) :
      ((aliceTable d).bind fun ta ↦ (bobTable d).map fun tb ↦
        if ta (x,z,index d z x y) && tb (y,z,index d z x y) then some (z,index d z x y) else none) =
      (LocalRejection.coin (d.aliceAccept x z (index d z x y)) (d.alice_nonneg _ _ _) (d.alice_le_one _ _ _)).bind fun a ↦
        (LocalRejection.coin (d.bobAccept y z (index d z x y)) (d.bob_nonneg _ _ _) (d.bob_le_one _ _ _)).map fun b ↦
          if a && b then some (z,index d z x y) else none := by
    have ha := LocalRejection.table_eval (fun i : X × (Z × Fin (C + 1)) ↦ d.aliceAccept i.1 i.2.1 i.2.2)
      (fun i ↦ d.alice_nonneg i.1 i.2.1 i.2.2) (fun i ↦ d.alice_le_one i.1 i.2.1 i.2.2) (x,z,index d z x y)
    have hb := LocalRejection.table_eval (fun i : Y × (Z × Fin (C + 1)) ↦ d.bobAccept i.1 i.2.1 i.2.2)
      (fun i ↦ d.bob_nonneg i.1 i.2.1 i.2.2) (fun i ↦ d.bob_le_one i.1 i.2.1 i.2.2) (y,z,index d z x y)
    rw [← ha, ← hb, PMF.bind_map]
    simp only [PMF.map_comp, Function.comp_def]
    rfl
  simp only [Protocol.viewLaw, Protocol.seedLaw, PMF.map_comp, PMF.map_bind, Function.comp_def]
  change d.proposal.bind (fun z ↦ (aliceTable d).bind fun ta ↦ (bobTable d).map fun tb ↦
    decode C (z, (((protocol d).tree z).run (x,ta) (y,tb)).1)) = _
  simp_rw [decoded_run]
  exact congrArg (PMF.bind d.proposal) (funext he)

end BBCR.IndexedRejection
