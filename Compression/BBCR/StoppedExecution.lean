module

public import BBCR.StoppingFrontier

/-! A first-hit sampler with the actual prefix transition probabilities is
exactly the stopped conditional execution, including persistent private seeds. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.StoppingFrontier

variable {Ω : Type*} [Fintype Ω]

noncomputable def prefixProbability (ν : PMF Ω) (T : Ω → List Bool) (s : List Bool) : ℝ :=
  mass (ν.map (fun ω ↦ (T ω).take s.length)) s

noncomputable def stoppedExecution (ν : PMF Ω) (T : Ω → List Bool)
    (n : ℕ) (halt : List Bool → Bool) (s : List Bool) : PMF (List Bool) :=
  (FiniteCondition.law ν (fun ω ↦ (T ω).take s.length) s).map
    (fun ω ↦ hit n halt s ((T ω).drop s.length))

omit [Fintype Ω] in
theorem take_drop_prefix (s w bits : List Bool) :
    bits.take s.length = s ∧ w.IsPrefix (bits.drop s.length) ↔ (s ++ w).IsPrefix bits := by
  constructor
  · rintro ⟨hs,hw⟩
    have he : s ++ bits.drop s.length = bits := by
      simpa only [hs] using List.take_append_drop s.length bits
    rw [← he]
    exact (List.prefix_append_right_inj s).mpr hw
  · intro h
    have hs := (List.prefix_append s w).trans h
    refine ⟨(List.prefix_iff_eq_take.mp hs).symm,?_⟩
    have hh := h
    rw [List.prefix_append_drop hs] at hh
    exact (List.prefix_append_right_inj s).mp hh

/-- On a frontier atom, the stopped observation has exactly its conditional
prefix probability. All normalization is inherited from finite conditioning. -/
theorem weighted_stopped_mass (ν : PMF Ω) (T : Ω → List Bool)
    (n : ℕ) (halt : List Bool → Bool) (s w : List Bool)
    (hw : w ∈ paths n halt s) :
    prefixProbability ν T s * mass (stoppedExecution ν T n halt s) w =
      prefixProbability ν T (s ++ w) := by
  rw [prefixProbability, stoppedExecution, FiniteCondition.weighted_observe,
    prefixProbability, mass_map_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have he : ((T ω).take s.length = s ∧ hit n halt s ((T ω).drop s.length) = w) ↔
      (T ω).take (s ++ w).length = s ++ w := by
    rw [hit_eq_iff n halt s w _ hw, take_drop_prefix,
      List.prefix_iff_eq_take, eq_comm]
  simp only [he]
  split_ifs <;> rfl

theorem stopped_mass_eq_zero_of_not_mem (ν : PMF Ω) (T : Ω → List Bool)
    (n : ℕ) (halt : List Bool → Bool) (s w : List Bool)
    (hs : 0 < prefixProbability ν T s)
    (hlen : ∀ ω, (T ω).length ≤ n) (hend : ∀ ω, halt (T ω) = true)
    (hw : w ∉ paths n halt s) : mass (stoppedExecution ν T n halt s) w = 0 := by
  rw [stoppedExecution, mass_map_sum]
  apply Finset.sum_eq_zero
  intro ω _
  by_cases he : hit n halt s ((T ω).drop s.length) = w
  · simp only [he, ite_true]
    by_contra hn
    have hf : (T ω).take s.length = s := by
      have hh := FiniteCondition.mass_law_of_pos ν (fun ω ↦ (T ω).take s.length) s hs ω
      by_contra hf
      rw [ite_eq_right hf, zero_div] at hh
      exact hn hh
    have hp : s.IsPrefix (T ω) := List.prefix_iff_eq_take.mpr hf.symm
    have hm := hit_mem n halt s ((T ω).drop s.length)
      (by simp only [List.length_drop]; have hh := hlen ω; omega)
      (by rw [← List.prefix_append_drop hp]; exact hend ω)
    exact hw (he ▸ hm)
  · simp only [he, ite_false]

/-- A recursively sampled frontier law equals the original experiment stopped
at that frontier, conditional on the starting prefix. No fresh-private-seed
normalization is assumed. -/
theorem law_eq_stoppedExecution (ν : PMF Ω) (T : Ω → List Bool)
    (n : ℕ) (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (hstep : ∀ s, halt s = false → ∀ b,
      prefixProbability ν T s * mass (K s) b = prefixProbability ν T (s ++ [b]))
    (s : List Bool) (hs : 0 < prefixProbability ν T s)
    (hlen : ∀ ω, (T ω).length ≤ n) (hend : ∀ ω, halt (T ω) = true) :
    law n halt K s = stoppedExecution ν T n halt s := by
  apply PMF.ext
  intro w
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change mass (law n halt K s) w = mass (stoppedExecution ν T n halt s) w
  by_cases hw : w ∈ paths n halt s
  · apply mul_left_cancel₀ hs.ne'
    rw [weighted_mass_law n halt K _ hstep, ite_eq_left hw,
      weighted_stopped_mass ν T n halt s w hw]
  · rw [mass_eq_zero_of_not_mem n halt K s w hw,
      stopped_mass_eq_zero_of_not_mem ν T n halt s w hs hlen hend hw]

end BBCR.StoppingFrontier
