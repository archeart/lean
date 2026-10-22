module

public import BBCR.Simulation

/-! Finite event probabilities and the coupling bound for deterministic
observations of one shared sample. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR

variable {Ω A : Type*} [Fintype Ω]

omit [Fintype Ω] in
theorem map_constant (p : PMF Ω) (a : A) : p.map (fun _ ↦ a) = PMF.pure a := PMF.map_const p a

noncomputable def probability (p : PMF Ω) (E : Ω → Prop) : ℝ :=
  ∑ ω, if E ω then mass p ω else 0

theorem probability_nonneg (p : PMF Ω) (E : Ω → Prop) : 0 ≤ probability p E := by
  unfold probability
  exact Finset.sum_nonneg fun ω _ ↦ by split_ifs <;> simp [mass_nonneg]

theorem probability_mono (p : PMF Ω) (E F : Ω → Prop) (h : ∀ ω, E ω → F ω) :
    probability p E ≤ probability p F := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω
  · simp [he, h ω he]
  · simp only [he, ite_false]
    split_ifs <;> simp [mass_nonneg]

theorem probability_le_one (p : PMF Ω) (E : Ω → Prop) : probability p E ≤ 1 := by
  calc
    _ ≤ ∑ ω, mass p ω := Finset.sum_le_sum fun ω _ ↦ by
      split_ifs <;> simp [mass_nonneg]
    _ = 1 := sum_mass p

theorem probability_map [Fintype A] (p : PMF Ω) (f : Ω → A) (E : A → Prop) :
    probability (p.map f) E = probability p (fun ω ↦ E (f ω)) := by
  simpa only [probability, mul_ite, mul_one, mul_zero] using
    Disjointness.Channel.sum_mass_map p f (fun a ↦ if E a then (1 : ℝ) else 0)

theorem probability_or_le (p : PMF Ω) (E F : Ω → Prop) :
    probability p (fun ω ↦ E ω ∨ F ω) ≤ probability p E + probability p F := by
  rw [probability, probability, probability, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω <;> by_cases hf : F ω <;> simp [he, hf, mass_nonneg]

theorem probability_exists_le {ι : Type*} [Fintype ι] (p : PMF Ω) (E : ι → Ω → Prop) :
    probability p (fun ω ↦ ∃ i, E i ω) ≤ ∑ i, probability p (E i) := by
  unfold probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : ∃ i, E i ω
  · obtain ⟨i, hi⟩ := he
    simp only [show (∃ i, E i ω) from ⟨i,hi⟩, ite_true]
    have hs := Finset.single_le_sum
      (f := fun i ↦ if E i ω then mass p ω else 0)
      (s := Finset.univ) (fun i _ ↦ by split_ifs <;> simp [mass_nonneg]) (Finset.mem_univ i)
    simpa only [hi, ite_true] using hs
  · simp only [he, ite_false]
    exact Finset.sum_nonneg fun i _ ↦ by split_ifs <;> simp [mass_nonneg]

theorem mass_map_sum (p : PMF Ω) (f : Ω → A) (a : A) :
    mass (p.map f) a = ∑ ω, if f ω = a then mass p ω else 0 := by
  rw [Disjointness.Channel.event_mass]
  simp [Finset.sum_filter]

/-- Finite Markov inequality. Nonnegativity is only required on the actual
support, so arbitrary definitions on null samples do not affect the bound. -/
theorem probability_le_expect_div (p : PMF Ω) (f : Ω → ℝ) (t : ℝ) (ht : 0 < t)
    (hf : ∀ ω, mass p ω ≠ 0 → 0 ≤ f ω) :
    probability p (fun ω ↦ t ≤ f ω) ≤ (∑ ω, mass p ω * f ω) / t := by
  apply (le_div_iff₀ ht).mpr
  rw [probability, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : t ≤ f ω
  · simp only [h, ite_true]
    exact mul_le_mul_of_nonneg_left h (mass_nonneg p ω)
  · simp only [h, ite_false, zero_mul]
    by_cases hp : mass p ω = 0
    · simp [hp]
    · exact mul_nonneg (mass_nonneg p ω) (hf ω hp)

/-- Two deterministic observations differ in total variation by at most their
probability of disagreement under the shared sample. -/
theorem variation_map_le_disagreement [Fintype A] (p : PMF Ω) (f g : Ω → A) :
    variation (p.map f) (p.map g) ≤ probability p (fun ω ↦ f ω ≠ g ω) := by
  have hp (ω : Ω) :
      (∑ a, |(if f ω = a then mass p ω else 0) -
        (if g ω = a then mass p ω else 0)|) =
      2 * (if f ω ≠ g ω then mass p ω else 0) := by
    by_cases he : f ω = g ω
    · simp [he]
    · have hpoint (a : A) :
          |(if f ω = a then mass p ω else 0) -
            (if g ω = a then mass p ω else 0)| =
          (if a = f ω then mass p ω else 0) + (if a = g ω then mass p ω else 0) := by
        by_cases hf : a = f ω <;> by_cases hg : a = g ω
        · exact (he (hf.symm.trans hg)).elim
        · simp [← hf, hg, Ne.symm hg, mass_nonneg]
        · simp [← hg, hf, Ne.symm hf, mass_nonneg]
        · simp [hf, hg, Ne.symm hf, Ne.symm hg]
      simp only [hpoint, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, ite_eq_left he]
      ring
  have hs : (∑ a, |mass (p.map f) a - mass (p.map g) a|) ≤
      2 * probability p (fun ω ↦ f ω ≠ g ω) := by
    simp_rw [mass_map_sum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ a, ∑ ω, |(if f ω = a then mass p ω else 0) -
          (if g ω = a then mass p ω else 0)| :=
        Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [hp, probability, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        by_cases h : f ω = g ω <;> simp [h]
  unfold variation
  linarith

end BBCR
