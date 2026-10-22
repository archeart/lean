module

public import BBCR.FirstDifferenceGeometry
public import BBCR.LikelihoodBounds

/-! Finite-horizon concentration for a backtracking search. A correct move
advances the score by one; every move changes it by at most one. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.NoisySearch

open FiniteAzuma FiniteDynamics

variable {S Ω : Type} [Fintype Ω]

noncomputable def delta (next : S → Ω → S) (V : S → ℝ) (s : S) (ω : Ω) : ℝ :=
  V (next s ω) - V s

noncomputable def mean (q : PMF Ω) (next : S → Ω → S) (V : S → ℝ) (s : S) : ℝ :=
  expect q (delta next V s)

noncomputable def centered (q : PMF Ω) (next : S → Ω → S) (V : S → ℝ) (s : S) (ω : Ω) : ℝ :=
  (mean q next V s - delta next V s ω) / 2

theorem mean_bounds (q : PMF Ω) (next : S → Ω → S) (V : S → ℝ) (s : S)
    (hb : ∀ ω, delta next V s ω ∈ Set.Icc (-1) 1) :
    mean q next V s ∈ Set.Icc (-1) 1 := by
  have hl := Finset.sum_le_sum (s := Finset.univ) fun ω _ ↦
    mul_le_mul_of_nonneg_left (hb ω).1 (mass_nonneg q ω)
  have hu := Finset.sum_le_sum (s := Finset.univ) fun ω _ ↦
    mul_le_mul_of_nonneg_left (hb ω).2 (mass_nonneg q ω)
  change expect q (fun _ ↦ (-1 : ℝ)) ≤ mean q next V s at hl
  change mean q next V s ≤ expect q (fun _ ↦ (1 : ℝ)) at hu
  rw [expect_const] at hl hu
  exact ⟨hl,hu⟩

theorem mean_ge_half (q : PMF Ω) (next : S → Ω → S) (V : S → ℝ)
    (good : S → Ω → Prop) (s : S)
    (hb : ∀ ω, -1 ≤ delta next V s ω)
    (hg : ∀ ω, good s ω → delta next V s ω = 1)
    (hp : probability q (fun ω ↦ ¬ good s ω) ≤ 1 / 4) :
    1 / 2 ≤ mean q next V s := by
  have he := Finset.sum_le_sum (s := Finset.univ) fun ω _ ↦
    mul_le_mul_of_nonneg_left (show (1 - 2 * if ¬ good s ω then (1 : ℝ) else 0) ≤ delta next V s ω from by
      by_cases hh : good s ω
      · simp [hh,hg ω hh]
      · simp only [hh,not_false_eq_true,ite_true]
        linarith [hb ω]) (mass_nonneg q ω)
  have hid : (∑ ω, mass q ω * (1 - 2 * if ¬ good s ω then (1 : ℝ) else 0)) =
      1 - 2 * probability q (fun ω ↦ ¬ good s ω) := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,sum_mass,probability]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> ring
  rw [hid] at he
  change _ ≤ mean q next V s at he
  linarith

theorem process_centered (q : PMF Ω) (next : S → Ω → S) (V : S → ℝ)
    (rank : S → ℕ) (N : ℕ)
    (hr : ∀ s ω, rank (next s ω) ≤ rank s + 1)
    (hb : ∀ s, rank s < N → ∀ ω, delta next V s ω ∈ Set.Icc (-1) 1)
    (n : ℕ) (s : S) (hs : rank s + n ≤ N) :
    (process q next (centered q next V) n s).Centered := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    have hh := mean_bounds q next V s (hb s (by omega))
    refine ⟨?_,?_,fun ω ↦ ih _ (by have h := hr s ω; omega)⟩
    · change expect q (fun ω ↦ (mean q next V s - delta next V s ω) / 2) = 0
      rw [expect_div]
      simp only [expect,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,sum_mass,one_mul]
      change (mean q next V s - mean q next V s) / 2 = 0
      ring
    · intro ω
      have hd := hb s (by omega) ω
      simp only [centered,Set.mem_Icc]
      constructor <;> linarith [hh.1,hh.2,hd.1,hd.2]

theorem progress (q : PMF Ω) (next : S → Ω → S) (V : S → ℝ)
    (rank : S → ℕ) (N : ℕ)
    (hr : ∀ s ω, rank (next s ω) ≤ rank s + 1)
    (hm : ∀ s, rank s < N → 1 / 2 ≤ mean q next V s)
    (n : ℕ) (s : S) (hs : rank s + n ≤ N) (bits : Fin n → Ω) :
    (n : ℝ) / 2 ≤ 2 * (process q next (centered q next V) n s).total bits +
      V (stateAfter next n s bits) - V s := by
  induction n generalizing s with
  | zero => simp [process,Process.total,stateAfter]
  | succ n ih =>
    have hh := ih (next s (bits 0)) (by have h := hr s (bits 0); omega) (Fin.tail bits)
    have hmean := hm s (by omega)
    simp only [process,Process.total,stateAfter,centered,delta,Nat.cast_add,Nat.cast_one]
    linarith

theorem failure_bound (q : PMF Ω) (next : S → Ω → S) (V : S → ℝ)
    (rank : S → ℕ) (N : ℕ)
    (hr : ∀ s ω, rank (next s ω) ≤ rank s + 1)
    (hb : ∀ s, rank s < N → ∀ ω, delta next V s ω ∈ Set.Icc (-1) 1)
    (hm : ∀ s, rank s < N → 1 / 2 ≤ mean q next V s)
    (n : ℕ) (hn : 0 < n) (s : S) (hs : rank s + n ≤ N) (hV : V s = 0)
    (t : ℝ) (ht : t ≤ n / 4) :
    probability (process q next (centered q next V) n s).law
      (fun bits ↦ V (stateAfter next n s bits) < t) ≤ Real.exp (-(n : ℝ) / 128) := by
  let P := process q next (centered q next V) n s
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := P.azuma (process_centered q next V rank N hr hb n s hs)
    (4 * n) ((n : ℝ) / 8) (by positivity) (by positivity)
    (fun bits ↦ (energy q next (centered q next V) n s bits).le)
  have he : -2 * ((n : ℝ) / 8) ^ 2 / (4 * n) = -(n : ℝ) / 128 := by
    field_simp
    ring
  rw [he] at hh
  refine le_trans ?_ hh
  rw [show P.tailMass ((n : ℝ) / 8) = probability P.law (fun bits ↦ (n : ℝ) / 8 ≤ P.total bits) by
    simp only [Process.tailMass,probability,Finset.sum_filter]]
  apply probability_mono
  intro bits hbits
  have hp := progress q next V rank N hr hm n s hs bits
  rw [hV] at hp
  change (n : ℝ) / 8 ≤ (process q next (centered q next V) n s).total bits
  linarith

end BBCR.NoisySearch
