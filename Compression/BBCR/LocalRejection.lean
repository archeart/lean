module

public import BBCR.BoundedRejection
public import BBCR.FiniteCoupling
public import Disjointness.ProductReplacement

/-! Finite private random tables implement arbitrary local acceptance
probabilities. The actual trial communicates exactly two bits. -/

@[expose] public section

open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR.LocalRejection

noncomputable def coin (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b ↦ ENNReal.ofReal (if b then a else 1 - a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ ↦ by cases b <;> simp [ha₀, ha₁])]
    simp)

@[simp] theorem mass_coin_true (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    mass (coin a ha₀ ha₁) true = a := ENNReal.toReal_ofReal ha₀

@[simp] theorem mass_coin_false (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    mass (coin a ha₀ ha₁) false = 1 - a := ENNReal.toReal_ofReal (sub_nonneg.mpr ha₁)

def tree {A B : Type*} (a : A → Bool) (b : B → Bool) : Tree A B :=
  .alice a (.bob b (.leaf false) (.leaf false)) (.bob b (.leaf false) (.leaf true))

theorem tree_run {A B : Type*} (a : A → Bool) (b : B → Bool) (x : A) (y : B) :
    (tree a b).run x y = ([a x,b y], a x && b y) := by
  cases ha : a x <;> cases hb : b y <;> simp [tree, Tree.run, ha, hb]

@[simp] theorem tree_depth {A B : Type*} (a : A → Bool) (b : B → Bool) :
    (tree a b).depth = 2 := rfl

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

noncomputable def table {I : Type} [Fintype I] (a : I → ℝ)
    (ha₀ : ∀ i, 0 ≤ a i) (ha₁ : ∀ i, a i ≤ 1) : PMF (I → Bool) :=
  pi (fun i ↦ coin (a i) (ha₀ i) (ha₁ i))

theorem table_eval {I : Type} [Fintype I] (a : I → ℝ)
    (ha₀ : ∀ i, 0 ≤ a i) (ha₁ : ∀ i, a i ≤ 1) (i : I) :
    (table a ha₀ ha₁).map (fun t ↦ t i) = coin (a i) (ha₀ i) (ha₁ i) :=
  pi_map_eval _ i

noncomputable def protocol (p : PMF Z) (a : X → Z → ℝ) (b : Y → Z → ℝ)
    (ha₀ : ∀ x z, 0 ≤ a x z) (ha₁ : ∀ x z, a x z ≤ 1)
    (hb₀ : ∀ y z, 0 ≤ b y z) (hb₁ : ∀ y z, b y z ≤ 1) :
    Protocol X Y Z ((X × Z) → Bool) ((Y × Z) → Bool) where
  publicLaw := p
  aliceLaw := table (fun i ↦ a i.1 i.2) (fun i ↦ ha₀ i.1 i.2) (fun i ↦ ha₁ i.1 i.2)
  bobLaw := table (fun i ↦ b i.1 i.2) (fun i ↦ hb₀ i.1 i.2) (fun i ↦ hb₁ i.1 i.2)
  tree z := tree (fun xt ↦ xt.2 (xt.1,z)) (fun yt ↦ yt.2 (yt.1,z))

def decode (v : Z × List Bool) : Option Z :=
  if v.2.getD 0 false && v.2.getD 1 false then some v.1 else none

theorem cost_le (p : PMF Z) (a : X → Z → ℝ) (b : Y → Z → ℝ)
    (ha₀ : ∀ x z, 0 ≤ a x z) (ha₁ : ∀ x z, a x z ≤ 1)
    (hb₀ : ∀ y z, 0 ≤ b y z) (hb₁ : ∀ y z, b y z ≤ 1) :
    (protocol p a b ha₀ ha₁ hb₀ hb₁).cost ≤ 2 := by
  apply Finset.sup_le
  intro z _
  exact le_rfl

theorem coinTrial_eq_attempt (p : PMF Z) (a b : Z → ℝ)
    (ha₀ : ∀ z, 0 ≤ a z) (ha₁ : ∀ z, a z ≤ 1)
    (hb₀ : ∀ z, 0 ≤ b z) (hb₁ : ∀ z, b z ≤ 1) :
    (p.bind fun z ↦ (coin (a z) (ha₀ z) (ha₁ z)).bind fun ba ↦
      (coin (b z) (hb₀ z) (hb₁ z)).map fun bb ↦ if ba && bb then some z else none) =
      Rejection.attempt p (fun z ↦ a z * b z)
        (fun z ↦ mul_nonneg (ha₀ z) (hb₀ z))
        (fun z ↦ (mul_le_mul (ha₁ z) (hb₁ z) (hb₀ z) (by norm_num)).trans_eq (mul_one 1)) := by
  apply PMF.ext
  intro o
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change mass (p.bind _) o = mass (Rejection.attempt p _ _ _) o
  rw [Disjointness.Channel.mass_bind]
  have hm (z : Z) : mass ((coin (a z) (ha₀ z) (ha₁ z)).bind fun ba ↦
      (coin (b z) (hb₀ z) (hb₁ z)).map fun bb ↦ if ba && bb then some z else none) o =
      if o = some z then a z * b z else if o = none then 1 - a z * b z else 0 := by
    rw [Disjointness.Channel.mass_bind, Fintype.sum_bool]
    simp only [mass_map_sum, Fintype.sum_bool, mass_coin_true, mass_coin_false]
    cases o with
    | none => simp; ring
    | some w =>
      by_cases hw : w = z
      · subst w; simp
      · simp [hw, Ne.symm hw]
  simp_rw [hm]
  cases o with
  | none =>
    rw [Rejection.mass_attempt_none]
    simp only [reduceCtorEq, ite_false, ite_true, mul_sub, mul_one,
      Finset.sum_sub_distrib, sum_mass, Rejection.rate]
  | some w =>
    rw [Rejection.mass_attempt_some]
    simp only [Option.some.injEq, reduceCtorEq, ite_false, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]


theorem decoded_law (p : PMF Z) (a : X → Z → ℝ) (b : Y → Z → ℝ)
    (ha₀ : ∀ x z, 0 ≤ a x z) (ha₁ : ∀ x z, a x z ≤ 1)
    (hb₀ : ∀ y z, 0 ≤ b y z) (hb₁ : ∀ y z, b y z ≤ 1) (x : X) (y : Y) :
    ((protocol p a b ha₀ ha₁ hb₀ hb₁).viewLaw x y).map decode =
      Rejection.attempt p (fun z ↦ a x z * b y z)
        (fun z ↦ mul_nonneg (ha₀ x z) (hb₀ y z))
        (fun z ↦ (mul_le_mul (ha₁ x z) (hb₁ y z) (hb₀ y z) (by norm_num)).trans_eq (mul_one 1)) := by
  let A := table (fun i : X × Z ↦ a i.1 i.2) (fun i ↦ ha₀ i.1 i.2) (fun i ↦ ha₁ i.1 i.2)
  let B := table (fun i : Y × Z ↦ b i.1 i.2) (fun i ↦ hb₀ i.1 i.2) (fun i ↦ hb₁ i.1 i.2)
  have he (z : Z) :
      (A.bind fun ta ↦ B.map fun tb ↦ if ta (x,z) && tb (y,z) then some z else none) =
      (coin (a x z) (ha₀ x z) (ha₁ x z)).bind fun ba ↦
        (coin (b y z) (hb₀ y z) (hb₁ y z)).map fun bb ↦ if ba && bb then some z else none := by
    have hA := table_eval (fun i : X × Z ↦ a i.1 i.2) (fun i ↦ ha₀ i.1 i.2) (fun i ↦ ha₁ i.1 i.2) (x,z)
    have hB := table_eval (fun i : Y × Z ↦ b i.1 i.2) (fun i ↦ hb₀ i.1 i.2) (fun i ↦ hb₁ i.1 i.2) (y,z)
    rw [← hA, ← hB, PMF.bind_map]
    simp only [PMF.map_comp, Function.comp_def]
    rfl
  have hrepr : ((protocol p a b ha₀ ha₁ hb₀ hb₁).viewLaw x y).map decode =
      p.bind (fun z ↦ (coin (a x z) (ha₀ x z) (ha₁ x z)).bind fun ba ↦
        (coin (b y z) (hb₀ y z) (hb₁ y z)).map fun bb ↦ if ba && bb then some z else none) := by
    simp only [Protocol.viewLaw, Protocol.seedLaw, PMF.map_comp, PMF.map_bind, protocol,
      Function.comp_def, tree_run, decode, List.getD_cons_zero, List.getD_cons_succ]
    exact congrArg (PMF.bind p) (funext he)
  rw [hrepr]
  exact coinTrial_eq_attempt p (a x) (b y) (ha₀ x) (ha₁ x) (hb₀ y) (hb₁ y)

end BBCR.LocalRejection
