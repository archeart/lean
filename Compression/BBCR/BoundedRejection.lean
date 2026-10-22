module

public import BBCR.Rejection
public import Disjointness.BinaryInformation

/-! A bounded rejection sampler with proved failure and output probabilities. -/

@[expose] public section

open Disjointness Disjointness.Hellinger

namespace BBCR.Rejection

variable {A : Type*} [Fintype A]

theorem mass_pure {B : Type*} (x y : B) [DecidableEq B] :
    mass (PMF.pure x) y = if y = x then 1 else 0 := by
  by_cases h : y = x <;> simp [mass, PMF.pure_apply, h]

/-- One actual trial: success returns the proposal, rejection returns `none`. -/
noncomputable def attempt (p : PMF A) (a : A → ℝ)
    (ha₀ : ∀ x, 0 ≤ a x) (ha₁ : ∀ x, a x ≤ 1) : PMF (Option A) :=
  PMF.ofFintype (fun o ↦ ENNReal.ofReal (match o with
    | none => 1 - rate p a
    | some x => mass p x * a x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ ↦ by
      cases o with
      | none => exact sub_nonneg.mpr (rate_le_one p a ha₁)
      | some x => exact mul_nonneg (mass_nonneg p x) (ha₀ x))]
    rw [Fintype.sum_option]
    change ENNReal.ofReal (1 - rate p a + rate p a) = 1
    simp)

@[simp] theorem mass_attempt_none (p : PMF A) (a : A → ℝ)
    (ha₀ : ∀ x, 0 ≤ a x) (ha₁ : ∀ x, a x ≤ 1) :
    mass (attempt p a ha₀ ha₁) none = 1 - rate p a :=
  ENNReal.toReal_ofReal (sub_nonneg.mpr (rate_le_one p a ha₁))

@[simp] theorem mass_attempt_some (p : PMF A) (a : A → ℝ)
    (ha₀ : ∀ x, 0 ≤ a x) (ha₁ : ∀ x, a x ≤ 1) (x : A) :
    mass (attempt p a ha₀ ha₁) (some x) = mass p x * a x :=
  ENNReal.toReal_ofReal (mul_nonneg (mass_nonneg p x) (ha₀ x))

/-- Repeat independent trials at most `n` times; the failure outcome is explicit. -/
noncomputable def bounded (p : PMF A) (a : A → ℝ)
    (ha₀ : ∀ x, 0 ≤ a x) (ha₁ : ∀ x, a x ≤ 1) : ℕ → PMF (Option A)
  | 0 => PMF.pure none
  | n + 1 => (attempt p a ha₀ ha₁).bind fun o ↦ match o with
      | none => bounded p a ha₀ ha₁ n
      | some x => PMF.pure (some x)

@[simp] theorem mass_bounded_none (p : PMF A) (a : A → ℝ)
    (ha₀ : ∀ x, 0 ≤ a x) (ha₁ : ∀ x, a x ≤ 1) (n : ℕ) :
    mass (bounded p a ha₀ ha₁ n) none = (1 - rate p a) ^ n := by
  classical
  induction n with
  | zero => simp [bounded, mass]
  | succ n ih =>
    rw [bounded, Disjointness.Channel.mass_bind, Fintype.sum_option]
    simp [mass_pure, ih, pow_succ, mul_comm]

/-- Conditional on success, a bounded sampler has exactly the accepted law.
Its only approximation is the separately quantified failure outcome. -/
theorem mass_bounded_some (p : PMF A) (a : A → ℝ)
    (ha₀ : ∀ x, 0 ≤ a x) (ha₁ : ∀ x, a x ≤ 1)
    (hr : 0 < rate p a) (n : ℕ) (x : A) :
    mass (bounded p a ha₀ ha₁ n) (some x) =
      (1 - (1 - rate p a) ^ n) * mass (accepted p a ha₀ hr) x := by
  classical
  induction n with
  | zero => simp [bounded, mass]
  | succ n ih =>
    rw [bounded, Disjointness.Channel.mass_bind, Fintype.sum_option]
    have hsome : (∑ y, mass (attempt p a ha₀ ha₁) (some y) *
        mass (PMF.pure (some y)) (some x)) = mass p x * a x := by
      simp only [mass_pure, Option.some.injEq, mass_attempt_some]
      simp [mul_ite]
    rw [hsome, mass_attempt_none, ih, mass_accepted, pow_succ]
    field_simp
    ring

end BBCR.Rejection
