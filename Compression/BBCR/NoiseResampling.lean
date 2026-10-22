module

public import BBCR.SmoothingCoupling
public import Disjointness.ProductReplacement

/-! The noise law is a genuine product law, not merely a law with the correct
one-coordinate marginals. Resampling a single correctness bit preserves it. -/

@[expose] public section

open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger
open scoped Classical

namespace BBCR.FiniteAzuma.Process

variable {A : Type*} [Fintype A]

theorem iid_law (p : PMF A) (f : A → ℝ) (lo hi : ℝ) (n : ℕ) :
    (iid p f lo hi n).law = pi (fun _ : Fin n ↦ p) := by
  induction n with
  | zero =>
    apply PMF.ext
    intro v
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    simp [iid, law, pi_apply, hv, PMF.pure_apply]
  | succ n ih =>
    apply PMF.ext
    intro v
    rw [iid, law, PMF.bind_apply, pi_apply, Fin.prod_univ_succ]
    have he (x : A) : ((iid p f lo hi n).law.map (Fin.cons x)) v =
        if x = v 0 then (iid p f lo hi n).law (Fin.tail v) else 0 := by
      rw [PMF.map_apply]
      have hc (w : Fin n → A) : v = Fin.cons x w ↔ x = v 0 ∧ w = Fin.tail v := by
        constructor
        · intro h
          exact ⟨(congrFun h 0).symm, (congrArg Fin.tail h).symm⟩
        · rintro ⟨rfl,rfl⟩
          exact (Fin.cons_self_tail v).symm
      simp only [hc, ite_and]
      by_cases hx : x = v 0 <;> simp [hx]
    simp_rw [he]
    simp only [mul_ite, mul_zero, tsum_ite_eq, ih, pi_apply, Fin.tail]

end BBCR.FiniteAzuma.Process

namespace BBCR.SmoothingTree

def updateBit {C m : ℕ} (tape : Tape C m) (i : Fin (C + 1)) (j : Fin m) (b : Bool) : Tape C m :=
  Function.update tape i (Function.update (tape i) j b)

@[simp] theorem updateBit_at {C m : ℕ} (tape : Tape C m) (i : Fin (C + 1)) (j : Fin m) (b : Bool) :
    updateBit tape i j b i j = b := by simp [updateBit]

theorem updateBit_other_block {C m : ℕ} (tape : Tape C m) (i i' : Fin (C + 1))
    (j : Fin m) (b : Bool) (hi : i' ≠ i) : updateBit tape i j b i' = tape i' :=
  Function.update_of_ne hi _ _

end BBCR.SmoothingTree

namespace BBCR.SmoothingCoupling

open SmoothingTree

theorem tapeLaw_product (C m : ℕ) (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    tapeLaw C m β hβ₀ hβ₁ =
      pi (fun _ : Fin (C + 1) ↦ pi (fun _ : Fin m ↦ SmoothingNoise.coin β hβ₀ hβ₁)) := by
  simp only [tapeLaw, SmoothingNoise.block, FiniteAzuma.Process.iid_law]

theorem tapeLaw_resample (C m : ℕ) (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2)
    (i : Fin (C + 1)) (j : Fin m) :
    (joint (SmoothingNoise.coin β hβ₀ hβ₁) (fun _ ↦ tapeLaw C m β hβ₀ hβ₁)).map
      (fun z ↦ updateBit z.2 i j z.1) = tapeLaw C m β hβ₀ hβ₁ := by
  rw [tapeLaw_product]
  let c := SmoothingNoise.coin β hβ₀ hβ₁
  let q := pi (fun _ : Fin m ↦ c)
  have hinner : (joint c (fun _ ↦ q)).map (fun z ↦ Function.update z.2 j z.1) = q := by
    dsimp only [q]
    rw [pi_replace]
    congr 1
    funext k
    simp
  -- Split off the selected block; its internal coordinate is resampled first.
  apply map_equiv_injective (Equiv.funSplitAt i (Fin m → Bool))
  rw [PMF.map_comp, pi_split]
  have hmap : (Equiv.funSplitAt i (Fin m → Bool)) ∘
      (fun z : Bool × Tape C m ↦ updateBit z.2 i j z.1) =
      (fun z ↦ (Function.update (z.2 i) j z.1, fun k : {k : Fin (C + 1) // k ≠ i} ↦ z.2 k)) := by
    funext z
    ext k
    · simp [updateBit, Equiv.funSplitAt_apply]
    · simp [updateBit, Equiv.funSplitAt_apply, k.2]
  rw [hmap]
  have hsplit := pi_split (fun _ : Fin (C + 1) ↦ q) i
  have hh := congrArg (fun law ↦ (joint c (fun _ ↦ law)).map
    (fun z ↦ (Function.update z.2.1 j z.1, z.2.2))) hsplit
  simp only [joint_eq_bind, PMF.map_bind, PMF.map_comp,
    Function.comp_def, Equiv.funSplitAt_apply] at hh
  change (joint c (fun _ ↦ pi (fun _ : Fin (C + 1) ↦ q))).map
    (fun z ↦ (Function.update (z.2 i) j z.1, fun k : {k : Fin (C + 1) // k ≠ i} ↦ z.2 k)) = _
  simp only [joint_eq_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [hh]
  have hinner' := congrArg (fun law ↦ joint law (fun _ ↦
    pi (fun _ : {k : Fin (C + 1) // k ≠ i} ↦ q))) hinner
  simpa only [joint_eq_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def, PMF.bind_bind] using hinner'

end BBCR.SmoothingCoupling
