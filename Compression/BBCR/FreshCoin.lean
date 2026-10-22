module

public import BBCR.NoiseResampling
public import BBCR.FiniteCondition

/-! Conditional noisy-bit bounds from an actual resampling identity, prefix
invariance, and the effect of the fresh bit on the next message. -/

@[expose] public section

open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger
open scoped Classical

namespace BBCR

variable {A B : Type*} [Fintype A] [Fintype B]

theorem joint_resample_left (p : PMF A) (q : PMF B) (c : PMF Bool) (u : A → Bool → A)
    (h : (joint c (fun _ ↦ p)).map (fun z ↦ u z.2 z.1) = p) :
    (joint c (fun _ ↦ joint p (fun _ ↦ q))).map
      (fun z ↦ (u z.2.1 z.1, z.2.2)) = joint p (fun _ ↦ q) := by
  have hh := congrArg (fun law ↦ joint law (fun _ ↦ q)) h
  simpa only [joint_eq_bind, PMF.map_bind, PMF.map_comp, PMF.bind_map, PMF.bind_bind,
    Function.comp_def] using hh

theorem joint_resample_right (p : PMF A) (q : PMF B) (c : PMF Bool) (u : B → Bool → B)
    (h : (joint c (fun _ ↦ q)).map (fun z ↦ u z.2 z.1) = q) :
    (joint c (fun _ ↦ joint p (fun _ ↦ q))).map
      (fun z ↦ (z.2.1, u z.2.2 z.1)) = joint p (fun _ ↦ q) := by
  have hh := congrArg (fun law ↦ joint p (fun _ ↦ law)) h
  simp only [joint_eq_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [PMF.bind_comm c p]
  simpa only [joint_eq_bind, PMF.map_bind, PMF.map_comp, PMF.bind_map, PMF.bind_bind,
    Function.comp_def] using hh

theorem resample_expectation (p : PMF A) (c : PMF Bool) (u : A → Bool → A)
    (h : (joint c (fun _ ↦ p)).map (fun z ↦ u z.2 z.1) = p) (F : A → ℝ) :
    (∑ a, mass p a * F a) = ∑ a, mass p a *
      (mass c false * F (u a false) + mass c true * F (u a true)) := by
  have hh := Disjointness.Channel.sum_mass_map (joint c (fun _ ↦ p)) (fun z ↦ u z.2 z.1) F
  rw [h, Fintype.sum_prod_type, Finset.sum_comm] at hh
  simp only [mass, joint_apply, ENNReal.toReal_mul, Fintype.sum_bool] at hh
  unfold mass
  rw [hh]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Fresh unbiased-in-history noisy response: conditioning on the public
history leaves the next true-bit probability between `1/2-β` and `1/2+β`. -/
theorem fresh_coin_conditional {H : Type*} (p : PMF A) (β : ℝ)
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) (u : A → Bool → A)
    (hresample : (joint (SmoothingNoise.coin β hβ₀ hβ₁) (fun _ ↦ p)).map
      (fun z ↦ u z.2 z.1) = p)
    (history : A → H) (message : A → Bool) (s : H)
    (hpos : 0 < mass (p.map history) s)
    (hstable : ∀ a bit, history (u a bit) = history a)
    (hflip : ∀ a, history a = s → message (u a false) = !(message (u a true))) :
    mass ((FiniteCondition.law p history s).map message) true ∈ Set.Icc (1 / 2 - β) (1 / 2 + β) := by
  let c := SmoothingNoise.coin β hβ₀ hβ₁
  let F : A → ℝ := fun a ↦ if history a = s ∧ message a = true then 1 else 0
  let G : A → ℝ := fun a ↦ mass c false * F (u a false) + mass c true * F (u a true)
  have he := resample_expectation p c u hresample F
  have hg (a : A) : (if history a = s then 1 / 2 - β else 0) ≤ G a ∧
      G a ≤ (if history a = s then 1 / 2 + β else 0) := by
    by_cases hh : history a = s
    · have hf := hflip a hh
      cases hm : message (u a true) <;>
        simp [G, F, c, hstable, hh, hf, hm, SmoothingNoise.coin_false, SmoothingNoise.coin_true]
      all_goals linarith
    · simp [G, F, hstable, hh]
  have hweight (v : ℝ) :
      (∑ a, mass p a * (if history a = s then v else 0)) = mass (p.map history) s * v := by
    rw [Disjointness.Channel.event_mass, Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hl := Finset.sum_le_sum (s := Finset.univ) fun a _ ↦
    mul_le_mul_of_nonneg_left (hg a).1 (mass_nonneg p a)
  have hu := Finset.sum_le_sum (s := Finset.univ) fun a _ ↦
    mul_le_mul_of_nonneg_left (hg a).2 (mass_nonneg p a)
  rw [hweight] at hl
  rw [hweight] at hu
  have hw := FiniteCondition.weighted_observe p history message s true
  have hF : (∑ a, mass p a * F a) =
      mass (p.map history) s * mass ((FiniteCondition.law p history s).map message) true := by
    rw [hw]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : history a = s ∧ message a = true <;> simp [F, h]
  change (∑ a, mass p a * F a) = ∑ a, mass p a * G a at he
  rw [← he, hF] at hl hu
  constructor <;> nlinarith

end BBCR
