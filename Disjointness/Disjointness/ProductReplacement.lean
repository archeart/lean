module

public import Disjointness.BinaryInformation

/-! Replacing one coordinate of a finite product distribution. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Disjointness.FiniteLaw

theorem map_equiv_injective {A B : Type*} (e : A ≃ B) : Function.Injective (PMF.map e) := by
  intro p q h
  have h' := congrArg (fun p ↦ p.map e.symm) h
  simpa only [PMF.map_comp, e.symm_comp_self, PMF.map_id] using h'

theorem joint_map_second {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : PMF A) (q : A → PMF B) (f : B → C) :
    (joint p q).map (fun z ↦ (z.1, f z.2)) = joint p (fun a ↦ (q a).map f) := by
  simp only [joint_eq_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Split a product law into one coordinate and its independent complement. -/
theorem pi_split (q : ι → PMF A) (i : ι) :
    (pi q).map (Equiv.funSplitAt i A) = joint (q i) (fun _ ↦ pi (fun j : {j // j ≠ i} ↦ q j)) := by
  ext ⟨a,x⟩
  rw [map_equiv_apply, joint_apply, pi_apply, Fintype.prod_eq_mul_prod_compl i]
  simp only [Equiv.funSplitAt_symm_apply]
  rw [Finset.prod_subtype (p := fun j ↦ j ≠ i) (F := inferInstance) _ (by simp)]
  simp only [pi_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp [j.2]

/-- Discarding one coordinate of a product leaves the product of the others. -/
theorem pi_restrict (q : ι → PMF A) (i : ι) :
    (pi q).map (fun x (j : {j // j ≠ i}) ↦ x j) = pi (fun j : {j // j ≠ i} ↦ q j) := by
  have h := congrArg (fun p ↦ p.map Prod.snd) (pi_split q i)
  rw [Channel.joint_map_snd, PMF.bind_const] at h
  simpa only [PMF.map_comp, Equiv.funSplitAt_apply, Function.comp_def] using h

/-- Freshly resampling one coordinate changes exactly that marginal. -/
theorem pi_replace (q : ι → PMF A) (i : ι) (w : PMF A) :
    (joint w (fun _ ↦ pi q)).map (fun z ↦ Function.update z.2 i z.1) =
      pi (Function.update q i w) := by
  let e := Equiv.funSplitAt i A
  have hinj : Function.Injective (PMF.map e) := by
    intro p q h
    have h' := congrArg (fun p ↦ p.map e.symm) h
    simpa only [PMF.map_comp, e.symm_comp_self, PMF.map_id] using h'
  apply hinj
  rw [PMF.map_comp, pi_split]
  have hq : (fun j : {j // j ≠ i} ↦ Function.update q i w j) = (fun j : {j // j ≠ i} ↦ q j) := by
    funext j
    exact Function.update_of_ne j.2 _ _
  rw [Function.update_self, hq]
  have hf : ((Equiv.funSplitAt i A) ∘ (fun z : A × (ι → A) ↦ Function.update z.2 i z.1)) =
      (fun z ↦ (z.1, fun j : {j // j ≠ i} ↦ z.2 j)) := by
    funext z
    ext j
    · simp
    · simp [j.2]
  rw [hf, joint_eq_bind, PMF.map_bind, joint_eq_bind]
  simp only [PMF.map_comp, Function.comp_def]
  congr 1
  funext a
  change (pi q).map ((Prod.mk a) ∘ (fun x (j : {j // j ≠ i}) ↦ x j)) = _
  rw [← PMF.map_comp, pi_restrict]

end Disjointness.FiniteLaw

namespace Disjointness.Switch

open FiniteLaw Hellinger Channel

theorem switches_resample {n : ℕ} (i : Fin n) :
    (joint fair (fun _ ↦ switches n)).map (fun z ↦ Function.update z.2 i z.1) = switches n := by
  rw [switches, pi_replace]
  congr 1
  funext j
  simp

/-- Averaging the two selected-switch cases preserves the full switch average. -/
theorem average_resample {n : ℕ} (i : Fin n) (F : Bits n → ℝ) :
    (∑ d, mass (switches n) d *
      ((F (Function.update d i false) + F (Function.update d i true)) / 2)) =
      ∑ d, mass (switches n) d * F d := by
  have h := sum_mass_map (joint fair (fun _ ↦ switches n))
    (fun z ↦ Function.update z.2 i z.1) F
  rw [switches_resample] at h
  rw [h, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Fintype.sum_bool, mass, joint_apply, ENNReal.toReal_mul,
    fair_apply, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  ring

end Disjointness.Switch
