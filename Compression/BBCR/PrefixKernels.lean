module

public import BBCR.ProtocolPrefix

/-! Normalized next-message laws at execution prefixes. On positive-probability
prefixes, the law is proved to depend only on the sender's input. -/

@[expose] public section

open Disjointness Disjointness.Hellinger

namespace BBCR.Prefix

theorem ratio_mem_unit {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hvu : v ≤ u) :
    0 ≤ v / u ∧ v / u ≤ 1 := by
  constructor
  · exact div_nonneg hv hu
  · by_cases h : u = 0
    · simp [h]
    · exact (div_le_one (lt_of_le_of_ne hu (Ne.symm h))).mpr hvu

noncomputable def coin (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b ↦ ENNReal.ofReal (if b then q else 1 - q)) (by
    simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
    rw [← ENNReal.ofReal_add hq.1 (sub_nonneg.mpr hq.2)]
    simp)

@[simp] theorem mass_coin_true (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) : mass (coin q hq) true = q :=
  ENNReal.toReal_ofReal hq.1

@[simp] theorem mass_coin_false (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) : mass (coin q hq) false = 1 - q :=
  ENNReal.toReal_ofReal (sub_nonneg.mpr hq.2)

theorem coin_congr (q q' : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (hq' : 0 ≤ q' ∧ q' ≤ 1) (h : q = q') :
    coin q hq = coin q' hq' := by subst q'; rfl

namespace Protocol

variable {X Y R SA SB : Type*}

section Alice
variable [Fintype SA]

theorem aliceFactor_le_one (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (x : X) :
    aliceFactor p r s x ≤ 1 := by
  classical
  calc
    _ ≤ ∑ a, p.aliceLaw a := Finset.sum_le_sum fun a _ ↦ by split_ifs <;> simp
    _ = 1 := Disjointness.FiniteLaw.sum_pmf _

theorem aliceFactor_ne_top (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (x : X) :
    aliceFactor p r s x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (aliceFactor_le_one p r s x)

noncomputable def aliceReach (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (x : X) : ℝ :=
  (aliceFactor p r s x).toReal

theorem aliceReach_nonneg (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (x : X) :
    0 ≤ aliceReach p r s x := ENNReal.toReal_nonneg

theorem aliceReach_append_le (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (s : List Bool) (x : X) (bit : Bool) :
    aliceReach p r (s ++ [bit]) x ≤ aliceReach p r s x :=
  ENNReal.toReal_mono (aliceFactor_ne_top p r s x) (aliceFactor_append_le p r x s bit)

noncomputable def aliceNext (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (x : X) : PMF Bool :=
  coin (aliceReach p r (s ++ [true]) x / aliceReach p r s x)
    (ratio_mem_unit (aliceReach_nonneg p r s x) (aliceReach_nonneg p r (s ++ [true]) x)
      (aliceReach_append_le p r s x true))

theorem aliceReach_split (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool)
    (h : Tree.speaker (p.tree r) s = some .alice) (x : X) :
    aliceReach p r (s ++ [false]) x + aliceReach p r (s ++ [true]) x = aliceReach p r s x := by
  have hh := congrArg ENNReal.toReal (aliceFactor_split p r s h x)
  rw [ENNReal.toReal_add (aliceFactor_ne_top _ _ _ _) (aliceFactor_ne_top _ _ _ _)] at hh
  exact hh

end Alice

section Bob
variable [Fintype SB]

theorem bobFactor_le_one (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (y : Y) :
    bobFactor p r s y ≤ 1 := by
  classical
  calc
    _ ≤ ∑ b, p.bobLaw b := Finset.sum_le_sum fun b _ ↦ by split_ifs <;> simp
    _ = 1 := Disjointness.FiniteLaw.sum_pmf _

theorem bobFactor_ne_top (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (y : Y) :
    bobFactor p r s y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (bobFactor_le_one p r s y)

noncomputable def bobReach (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (y : Y) : ℝ :=
  (bobFactor p r s y).toReal

theorem bobReach_nonneg (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (y : Y) :
    0 ≤ bobReach p r s y := ENNReal.toReal_nonneg

theorem bobReach_append_le (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (s : List Bool) (y : Y) (bit : Bool) :
    bobReach p r (s ++ [bit]) y ≤ bobReach p r s y :=
  ENNReal.toReal_mono (bobFactor_ne_top p r s y) (bobFactor_append_le p r y s bit)

noncomputable def bobNext (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) (y : Y) : PMF Bool :=
  coin (bobReach p r (s ++ [true]) y / bobReach p r s y)
    (ratio_mem_unit (bobReach_nonneg p r s y) (bobReach_nonneg p r (s ++ [true]) y)
      (bobReach_append_le p r s y true))

theorem bobReach_split (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool)
    (h : Tree.speaker (p.tree r) s = some .bob) (y : Y) :
    bobReach p r (s ++ [false]) y + bobReach p r (s ++ [true]) y = bobReach p r s y := by
  have hh := congrArg ENNReal.toReal (bobFactor_split p r s h y)
  rw [ENNReal.toReal_add (bobFactor_ne_top _ _ _ _) (bobFactor_ne_top _ _ _ _)] at hh
  exact hh

end Bob

variable [Fintype SA] [Fintype SB]

noncomputable def reach (p : Disjointness.Protocol X Y R SA SB) (r : R) (x : X) (y : Y) (s : List Bool) : ℝ :=
  mass (law p r x y s.length) s

theorem reach_eq (p : Disjointness.Protocol X Y R SA SB) (r : R) (x : X) (y : Y) (s : List Bool) :
    reach p r x y s = aliceReach p r s x * bobReach p r s y := by
  rw [reach, mass, law_factorization, ENNReal.toReal_mul]
  rfl

omit [Fintype SA] [Fintype SB] in
theorem reach_nonneg (p : Disjointness.Protocol X Y R SA SB) (r : R) (x : X) (y : Y) (s : List Bool) :
    0 ≤ reach p r x y s := mass_nonneg _ _

theorem reach_append_le (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool) (bit : Bool) :
    reach p r x y (s ++ [bit]) ≤ reach p r x y s := by
  simp only [reach_eq]
  exact mul_le_mul (aliceReach_append_le p r s x bit) (bobReach_append_le p r s y bit)
    (bobReach_nonneg _ _ _ _) (aliceReach_nonneg _ _ _ _)

/-- A total version of the next-message law. At null prefixes the ratio is zero;
all correctness/locality statements below explicitly require positive reach. -/
noncomputable def next (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool) : PMF Bool :=
  coin (reach p r x y (s ++ [true]) / reach p r x y s)
    (ratio_mem_unit (reach_nonneg p r x y s) (reach_nonneg p r x y (s ++ [true]))
      (reach_append_le p r x y s true))

theorem next_eq_alice (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool)
    (howner : Tree.speaker (p.tree r) s = some .alice) (hpos : 0 < reach p r x y s) :
    next p r x y s = aliceNext p r s x := by
  unfold next aliceNext
  apply coin_congr
  have hb : bobReach p r s y ≠ 0 := by
    intro hb
    simp only [reach_eq, hb, mul_zero] at hpos
    linarith
  have ha : aliceReach p r s x ≠ 0 := by
    intro ha
    simp only [reach_eq, ha, zero_mul] at hpos
    linarith
  dsimp only [aliceReach, bobReach] at ha hb
  simp only [reach_eq, aliceReach, bobReach]
  rw [bobFactor_unchanged_of_alice p r s howner y true]
  field_simp [ha, hb]

theorem next_eq_bob (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool)
    (howner : Tree.speaker (p.tree r) s = some .bob) (hpos : 0 < reach p r x y s) :
    next p r x y s = bobNext p r s y := by
  unfold next bobNext
  apply coin_congr
  have ha : aliceReach p r s x ≠ 0 := by
    intro ha
    simp only [reach_eq, ha, zero_mul] at hpos
    linarith
  have hb : bobReach p r s y ≠ 0 := by
    intro hb
    simp only [reach_eq, hb, mul_zero] at hpos
    linarith
  dsimp only [aliceReach, bobReach] at ha hb
  simp only [reach_eq, aliceReach, bobReach]
  rw [aliceFactor_unchanged_of_bob p r s howner x true]
  field_simp [ha, hb]

theorem reach_split (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) :
    reach p r x y (s ++ [false]) + reach p r x y (s ++ [true]) = reach p r x y s := by
  cases who with
  | alice =>
    simp only [reach_eq, bobReach, bobFactor_unchanged_of_alice p r s howner]
    rw [← add_mul, aliceReach_split p r s howner]
  | bob =>
    simp only [reach_eq, aliceReach, aliceFactor_unchanged_of_bob p r s howner]
    rw [← mul_add, bobReach_split p r s howner]

/-- The normalized kernel reproduces both conditional extension probabilities
of the actual execution, rather than just a chosen Bernoulli parameter. -/
theorem mass_next (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (hpos : 0 < reach p r x y s) (bit : Bool) :
    mass (next p r x y s) bit = reach p r x y (s ++ [bit]) / reach p r x y s := by
  cases bit with
  | true => exact mass_coin_true _ _
  | false =>
    rw [next, mass_coin_false]
    have hs := reach_split p r x y s who howner
    apply (eq_div_iff hpos.ne').mpr
    field_simp
    linarith

/-- Unnormalized transition identity, also valid at null input/prefix pairs. -/
theorem weighted_mass_next (p : Disjointness.Protocol X Y R SA SB)
    (r : R) (x : X) (y : Y) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (bit : Bool) :
    reach p r x y s * mass (next p r x y s) bit = reach p r x y (s ++ [bit]) := by
  by_cases hp : 0 < reach p r x y s
  · rw [mass_next p r x y s who howner hp]
    field_simp
  · have hz : reach p r x y s = 0 := le_antisymm (le_of_not_gt hp) (reach_nonneg _ _ _ _ _)
    have hc : reach p r x y (s ++ [bit]) = 0 :=
      le_antisymm ((reach_append_le p r x y s bit).trans_eq hz) (reach_nonneg _ _ _ _ _)
    rw [hz, hc, zero_mul]

end Protocol
end BBCR.Prefix
