module

public import BBCR.ProtocolFamily
public import BBCR.LocalRejection

/-! Finite public fingerprints with exact independent-coordinate laws. -/

@[expose] public section

open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR.FiniteHashing

variable {I A : Type} [Fintype I] [Fintype A]

theorem pi_pair (q : I → PMF A) (i j : I) (hij : j ≠ i) :
    (pi q).map (fun row ↦ (row i,row j)) = joint (q i) (fun _ ↦ q j) := by
  have hh := congrArg (fun law ↦ law.map (fun z : A × ({k : I // k ≠ i} → A) ↦ (z.1,z.2 ⟨j,hij⟩))) (pi_split q i)
  rw [joint_map_second (q i) (fun _ ↦ pi (fun k : {k : I // k ≠ i} ↦ q k))
    (fun rest ↦ rest ⟨j,hij⟩), ProtocolIteration.pi_eval] at hh
  simpa only [PMF.map_comp,Function.comp_def,Equiv.funSplitAt_apply] using hh

noncomputable def uniform16 : PMF (Fin 16) := PMF.ofFintype (fun _ ↦ (16 : ENNReal)⁻¹) (by
  norm_num
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

@[simp] theorem uniform16_mass (a : Fin 16) : mass uniform16 a = 1 / 16 := by
  norm_num [uniform16,mass]

noncomputable def law (I : Type) [Fintype I] : PMF (I → Fin 16) := pi (fun _ ↦ uniform16)

omit [Fintype A] in
theorem collision (i j : I) (hij : i ≠ j) : probability (law I) (fun h ↦ h i = h j) = 1 / 16 := by
  have hh := pi_pair (fun _ : I ↦ uniform16) i j (Ne.symm hij)
  have hp := probability_map (law I) (fun h ↦ (h i,h j)) (fun z ↦ z.1 = z.2)
  unfold law at hp
  rw [hh, probability_joint] at hp
  have he : (fun a : Fin 16 ↦ probability uniform16 (fun b ↦ a = b)) = fun _ ↦ (1 / 16 : ℝ) := by
    funext a
    simp [probability]
  rw [he, FiniteAzuma.expect_const] at hp
  exact hp.symm

omit [Fintype A] in
theorem error_le (i j : I) :
    probability (law I) (fun h ↦ (h i = h j) ≠ (i = j)) ≤ 1 / 16 := by
  by_cases hij : i = j
  · subst j
    simp [probability]
  · have he : probability (law I) (fun h ↦ (h i = h j) ≠ (i = j)) = probability (law I) (fun h ↦ h i = h j) := by
      unfold probability
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : h i = h j <;> simp [hh,hij]
    rw [he,collision i j hij]

end BBCR.FiniteHashing
