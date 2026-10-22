module

public import BBCR.FiniteHashing
public import BBCR.FrontierLocation

/-! An actual five-bit public-coin equality test. Alice sends a four-bit
fingerprint and Bob publishes the comparison bit. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.FingerprintProtocol

variable {X Y I : Type}

theorem width16 : FrontierLocation.width 15 = 4 := by decide

noncomputable def tree (h : I → Fin 16) (a : X → I) (b : Y → I)
    (k : Bool → Tree X Y) : Tree X Y :=
  TreeBlocks.alice (FrontierLocation.width 15) (fun x ↦ FrontierLocation.encode 15 (h (a x)))
    (fun bits ↦ .bob (fun y ↦ decide (FrontierLocation.decode 15 bits = h (b y))) (k false) (k true))

theorem run (h : I → Fin 16) (a : X → I) (b : Y → I)
    (k : Bool → Tree X Y) (x : X) (y : Y) :
    (tree h a b k).run x y =
      (List.ofFn (FrontierLocation.encode 15 (h (a x))) ++
        (decide (h (a x) = h (b y)) :: ((k (decide (h (a x) = h (b y)))).run x y).1),
      ((k (decide (h (a x) = h (b y)))).run x y).2) := by
  rw [tree,TreeBlocks.run_alice,FrontierLocation.decode_encode]
  cases he : decide (h (a x) = h (b y)) <;> simp [Tree.run,he]

theorem depth_le (h : I → Fin 16) (a : X → I) (b : Y → I)
    (k : Bool → Tree X Y) (d : ℕ) (hk : ∀ bit, (k bit).depth ≤ d) :
    (tree h a b k).depth ≤ 5 + d := by
  apply (TreeBlocks.depth_alice_le _ _ _ (d + 1) ?_).trans
  · rw [width16]
    omega
  · intro bits
    simp only [Tree.depth]
    have h₀ := hk false
    have h₁ := hk true
    omega

variable [Fintype I]

noncomputable def protocol (a : X → I) (b : Y → I) :
    Protocol X Y (I → Fin 16) Unit Unit where
  publicLaw := FiniteHashing.law I
  aliceLaw := PMF.pure ()
  bobLaw := PMF.pure ()
  tree h := (tree h a b (fun bit ↦ .leaf bit)).comap Prod.fst Prod.fst

theorem cost_le (a : X → I) (b : Y → I) : (protocol a b).cost ≤ 5 := by
  apply Finset.sup_le
  intro h _
  rw [protocol,Tree.depth_comap]
  exact (depth_le h a b (fun bit ↦ .leaf bit) 0 (fun _ ↦ le_rfl)).trans_eq (Nat.add_zero _)

theorem error_le (a : X → I) (b : Y → I) (x : X) (y : Y) :
    probability (FiniteHashing.law I)
      (fun h ↦ (((protocol a b).tree h).run (x,()) (y,())).2 ≠ decide (a x = b y)) ≤ 1 / 16 := by
  have hr (h : I → Fin 16) : (((protocol a b).tree h).run (x,()) (y,())).2 =
      decide (h (a x) = h (b y)) := by
    simp only [protocol,Tree.run_comap,run,Tree.run]
  simp only [hr]
  convert FiniteHashing.error_le (a x) (b y) using 2
  funext h
  by_cases ha : a x = b y <;> by_cases hh : h (a x) = h (b y) <;> simp [ha,hh]

end BBCR.FingerprintProtocol
