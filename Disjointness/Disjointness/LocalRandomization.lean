module

public import Disjointness.AndLowerBound
public import Disjointness.CoordinateInformation

/-! Local private preprocessing, with exact view and output laws. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Disjointness.Protocol

open FiniteLaw Hellinger Channel

variable {X Y X' Y' R SA SB A B : Type*}
  [Fintype R] [Fintype SA] [Fintype SB] [Fintype A] [Fintype B]

/-- Sample private padding independently and preprocess the two inputs locally.
The final Boolean relabeling uses no communication. -/
noncomputable def localRandomize (p : Protocol X Y R SA SB) (a : PMF A) (b : PMF B)
    (f : X' → A → X) (g : Y' → B → Y) (o : Bool → Bool) :
    Protocol X' Y' R (A × SA) (B × SB) where
  publicLaw := p.publicLaw
  aliceLaw := joint a (fun _ ↦ p.aliceLaw)
  bobLaw := joint b (fun _ ↦ p.bobLaw)
  tree r := ((p.tree r).comap (fun x ↦ (f x.1 x.2.1, x.2.2))
    (fun y ↦ (g y.1 y.2.1, y.2.2))).mapOutput o

variable (p : Protocol X Y R SA SB) (a : PMF A) (b : PMF B)
    (f : X' → A → X) (g : Y' → B → Y) (o : Bool → Bool)

@[simp] theorem localRandomize_cost : (p.localRandomize a b f g o).cost = p.cost := by
  simp only [cost, localRandomize, Tree.depth_mapOutput, Tree.depth_comap]

def randomViewEquiv : (p.localRandomize a b f g o).View ≃ p.View where
  toFun v := ⟨v.1, ⟨v.2.1, by simpa only [localRandomize, Tree.leafPaths_mapOutput, Tree.leafPaths_comap] using v.2.2⟩⟩
  invFun v := ⟨v.1, ⟨v.2.1, by simpa only [localRandomize, Tree.leafPaths_mapOutput, Tree.leafPaths_comap] using v.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup the independent original and padding seeds. -/
def randomSeedEquiv : (R × ((A × SA) × (B × SB))) ≃ ((A × B) × (R × (SA × SB))) where
  toFun s := ((s.2.1.1, s.2.2.1), (s.1, (s.2.1.2, s.2.2.2)))
  invFun s := (s.2.1, ((s.1.1, s.2.2.1), (s.1.2, s.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

theorem localRandomize_seedLaw :
    (p.localRandomize a b f g o).seedLaw.map randomSeedEquiv =
      joint (joint a (fun _ ↦ b)) (fun _ ↦ p.seedLaw) := by
  ext ⟨⟨u,v⟩,r,sa,sb⟩
  rw [map_equiv_apply]
  simp only [randomSeedEquiv, Equiv.coe_fn_symm_mk, seedLaw_apply, localRandomize, joint_apply]
  ring

theorem localRandomize_viewLaw (x : X') (y : Y') :
    ((p.localRandomize a b f g o).finiteViewLaw x y).map (p.randomViewEquiv a b f g o) =
      (joint a (fun _ ↦ b)).bind (fun z ↦ p.finiteViewLaw (f x z.1) (g y z.2)) := by
  have hr : (p.randomViewEquiv a b f g o) ∘
      ((p.localRandomize a b f g o).runView x y) =
      (fun s : (A × B) × (R × (SA × SB)) ↦ p.runView (f x s.1.1) (g y s.1.2) s.2) ∘
        randomSeedEquiv := by
    funext s
    apply p.forgetView_injective
    change (s.1, (((p.localRandomize a b f g o).tree s.1).run (x,s.2.1) (y,s.2.2)).1) =
      (s.1, ((p.tree s.1).run (f x s.2.1.1,s.2.1.2) (g y s.2.2.1,s.2.2.2)).1)
    simp [localRandomize]
  rw [finiteViewLaw, PMF.map_comp, hr, ← PMF.map_comp, localRandomize_seedLaw,
    joint_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, finiteViewLaw]

theorem localRandomize_outputLaw (x : X') (y : Y') :
    (p.localRandomize a b f g o).outputLaw x y =
      (joint a (fun _ ↦ b)).bind (fun z ↦ (p.outputLaw (f x z.1) (g y z.2)).map o) := by
  have hr : (fun s : R × ((A × SA) × (B × SB)) ↦
      (((p.localRandomize a b f g o).tree s.1).run (x,s.2.1) (y,s.2.2)).2) =
      (fun s : (A × B) × (R × (SA × SB)) ↦
        o (((p.tree s.2.1).run (f x s.1.1,s.2.2.1) (g y s.1.2,s.2.2.2)).2)) ∘
        randomSeedEquiv := by
    funext s
    simp [localRandomize, randomSeedEquiv]
  rw [outputLaw, hr, ← PMF.map_comp, localRandomize_seedLaw,
    joint_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, outputLaw]

end Disjointness.Protocol
