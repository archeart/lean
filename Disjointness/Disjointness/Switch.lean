module

public import Disjointness.ProbabilityTools
public import Disjointness.Target

/-!
# The BJKS switch distribution

Each switch is fair. If it is false, Alice's bit is zero and Bob's is fair;
if true, Alice's bit is fair and Bob's is zero. Coordinates are sampled
independently. The switch is an analysis variable, never a protocol input.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Disjointness.Switch

open FiniteLaw

noncomputable def fair : PMF Bool :=
  PMF.ofFintype (fun _ ↦ (2 : ℝ≥0∞)⁻¹) (by simp [ENNReal.mul_inv_cancel])

@[simp] theorem fair_apply (b : Bool) : fair b = (2 : ℝ≥0∞)⁻¹ := rfl

/-- A bit is fair when active, and identically zero otherwise. -/
noncomputable def bitLaw (active : Bool) : PMF Bool :=
  if active then fair else PMF.pure false

noncomputable def switches (n : ℕ) : PMF (Bits n) := pi (fun _ ↦ fair)

noncomputable def aliceLaw {n : ℕ} (d : Bits n) : PMF (Bits n) :=
  pi (fun i ↦ bitLaw (d i))

noncomputable def bobLaw {n : ℕ} (d : Bits n) : PMF (Bits n) :=
  pi (fun i ↦ bitLaw (!(d i)))

/-- Input law conditional on the full switch vector. -/
noncomputable def inputLaw {n : ℕ} (d : Bits n) : PMF (Bits n × Bits n) :=
  joint (aliceLaw d) (fun _ ↦ bobLaw d)

abbrev Sample (n : ℕ) := Bits n × (Bits n × Bits n)

/-- Joint law of `(D,(X,Y))`. -/
noncomputable def law (n : ℕ) : PMF (Sample n) := joint (switches n) inputLaw

@[simp] theorem switches_apply {n : ℕ} (d : Bits n) :
    switches n d = ((2 : ℝ≥0∞)⁻¹) ^ n := by
  simp [switches, pi_apply]

theorem switches_pos {n : ℕ} (d : Bits n) : switches n d ≠ 0 := by simp

/-- Exact product formula for the conditional input law. -/
theorem inputLaw_apply {n : ℕ} (d x y : Bits n) :
    inputLaw d (x, y) = ∏ i, bitLaw (d i) (x i) * bitLaw (!(d i)) (y i) := by
  simp [inputLaw, aliceLaw, bobLaw, Finset.prod_mul_distrib]

theorem law_apply {n : ℕ} (d x y : Bits n) :
    law n (d, (x, y)) = ∏ i, fair (d i) *
      (bitLaw (d i) (x i) * bitLaw (!(d i)) (y i)) := by
  simp only [law, joint_apply, switches, pi_apply, inputLaw_apply, Finset.prod_mul_distrib]

/-- All switch vectors have positive mass, and their conditional input law is exact. -/
theorem cond_switch {n : ℕ} (d : Bits n) :
    (law n).toMeasure[|Prod.fst ⁻¹' {d}] =
      (PMF.pure d).toMeasure.prod (inputLaw d).toMeasure := by
  rw [law, joint_cond_fst _ _ _ (switches_pos d), joint_const_toMeasure]

theorem inputLaw_indep {n : ℕ} (d : Bits n) :
    IndepFun Prod.fst Prod.snd (inputLaw d).toMeasure := by
  rw [inputLaw, joint_const_toMeasure]
  exact indepFun_fst_snd

/-- Grouping coordinate pairs is just a bijective relabeling. -/
def coordinatesEquiv (n : ℕ) : (Bits n × Bits n) ≃ (Fin n → Bool × Bool) where
  toFun xy i := (xy.1 i, xy.2 i)
  invFun z := (fun i ↦ (z i).1, fun i ↦ (z i).2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The conditional input law is a product over coordinate pairs as well as players. -/
theorem inputLaw_map_coordinates {n : ℕ} (d : Bits n) :
    (inputLaw d).map (coordinatesEquiv n) =
      pi (fun i ↦ joint (bitLaw (d i)) (fun _ ↦ bitLaw (!(d i)))) := by
  ext z
  rw [map_equiv_apply]
  simp only [coordinatesEquiv, Equiv.coe_fn_symm_mk, inputLaw_apply, pi_apply, joint, PMF.ofFintype_apply]

theorem inputLaw_iIndep {n : ℕ} (d : Bits n) :
    iIndepFun (fun i (xy : Bits n × Bits n) ↦ (xy.1 i, xy.2 i)) (inputLaw d).toMeasure := by
  have hm : (inputLaw d).toMeasure.map (coordinatesEquiv n) =
      Measure.pi (fun i ↦ (joint (bitLaw (d i)) (fun _ ↦ bitLaw (!(d i)))).toMeasure) := by
    rw [PMF.toMeasure_map _ _ .of_discrete, inputLaw_map_coordinates, pi_toMeasure]
  exact iIndep_pullback (show Measurable (coordinatesEquiv n) from .of_discrete) hm
    (fun _ ↦ measurable_pi_apply _) (iIndepFun_pi (fun _ ↦ aemeasurable_id))

/-- The input pairs at different coordinates are independent after fixing the switches. -/
theorem coordinates_condIndep {n : ℕ} (d : Bits n) :
    iIndepFun (fun i (s : Sample n) ↦ (s.2.1 i, s.2.2 i))
      ((law n).toMeasure[|Prod.fst ⁻¹' {d}]) := by
  rw [cond_switch]
  exact iIndep_pullback measurable_snd (by simp)
    (fun _ ↦ .of_discrete) (inputLaw_iIndep d)

/-- Alice and Bob's whole inputs are conditionally independent in PFR's sense. -/
theorem players_condIndep (n : ℕ) :
    CondIndepFun (fun s : Sample n ↦ s.2.1) (fun s ↦ s.2.2) Prod.fst (law n).toMeasure := by
  apply Filter.Eventually.of_forall
  intro d
  rw [cond_switch]
  exact indep_pullback measurable_snd (by simp) measurable_fst measurable_snd (inputLaw_indep d)

/-- Every input pair in the support is disjoint, including in dimension zero. -/
theorem disj_of_mem_support {n : ℕ} {d x y : Bits n}
    (h : (d, (x, y)) ∈ (law n).support) : disj x y = true := by
  have hp : ∀ i, bitLaw (d i) (x i) * bitLaw (!(d i)) (y i) ≠ 0 := by
    have hxy : inputLaw d (x, y) ≠ 0 := (mul_ne_zero_iff.mp h).2
    rw [inputLaw_apply] at hxy
    exact fun i ↦ (Finset.prod_ne_zero_iff.mp hxy) i (Finset.mem_univ i)
  simp only [disj, decide_eq_true_eq]
  intro i
  specialize hp i
  cases hd : d i <;> cases hx : x i <;> cases hy : y i <;>
    simp_all [bitLaw, PMF.pure_apply]

/-- Joint switch and input law for one coordinate. -/
noncomputable def coordinateLaw : PMF (Bool × (Bool × Bool)) :=
  joint fair (fun d ↦ joint (bitLaw d) (fun _ ↦ bitLaw (!d)))

def triplesEquiv (n : ℕ) : Sample n ≃ (Fin n → Bool × (Bool × Bool)) where
  toFun s i := (s.1 i, (s.2.1 i, s.2.2 i))
  invFun z := (fun i ↦ (z i).1, (fun i ↦ (z i).2.1, fun i ↦ (z i).2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full law consists of independent, identically distributed triples. -/
theorem law_map_triples (n : ℕ) :
    (law n).map (triplesEquiv n) = pi (fun _ : Fin n ↦ coordinateLaw) := by
  ext z
  rw [map_equiv_apply]
  simp only [triplesEquiv, Equiv.coe_fn_symm_mk, law_apply, pi_apply,
    coordinateLaw, joint, PMF.ofFintype_apply]

theorem law_map_coordinate {n : ℕ} (i : Fin n) :
    (law n).map (fun s ↦ (s.1 i, (s.2.1 i, s.2.2 i))) = coordinateLaw := by
  have h := congrArg (fun p ↦ p.map (Function.eval i)) (law_map_triples n)
  rw [pi_map_eval] at h
  simpa only [PMF.map_comp, Function.comp_def, triplesEquiv, Equiv.coe_fn_mk, Function.eval] using h

/-- The input marginal is `(00,01,10,11) ↦ (1/2,1/4,1/4,0)`. -/
theorem coordinate_input_probabilities (x y : Bool) :
    coordinateLaw.map Prod.snd (x, y) =
      if x then (if y then 0 else (4 : ℝ≥0∞)⁻¹)
      else (if y then (4 : ℝ≥0∞)⁻¹ else (2 : ℝ≥0∞)⁻¹) := by
  have hquarter : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ = 4⁻¹ := by
    have h := ENNReal.mul_inv (a := (2 : ℝ≥0∞)) (b := 2) (by simp) (by simp)
    norm_num at h
    exact h.symm
  have hhalf : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ + 2⁻¹ * 2⁻¹ = 2⁻¹ := by
    rw [← add_mul, ← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  cases x <;> cases y <;>
    norm_num [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, coordinateLaw,
      joint_apply, bitLaw, PMF.pure_apply, fair_apply]
  all_goals first | exact hhalf | exact hquarter

/-- A switch coordinate is fair and independent of all other switch coordinates. -/
theorem switches_iIndep (n : ℕ) :
    iIndepFun (fun i (d : Bits n) ↦ d i) (switches n).toMeasure := by
  rw [switches, pi_toMeasure]
  exact iIndepFun_pi (fun _ ↦ aemeasurable_id)

theorem switches_map_coordinate {n : ℕ} (i : Fin n) :
    (switches n).map (Function.eval i) = fair := pi_map_eval _ _

end Disjointness.Switch
