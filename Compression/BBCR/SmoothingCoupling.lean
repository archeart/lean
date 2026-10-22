module

public import BBCR.SmoothingProtocol
public import BBCR.SmoothingNoise

/-! The iid noise instantiation of the smoothing transformation. The original
private seeds remain private. The failure estimate is uniform in the input and
uses a union bound over both private tapes and all logical message positions. -/

@[expose] public section

open Disjointness Disjointness.FiniteLaw Disjointness.Hellinger
open scoped Classical

namespace BBCR.SmoothingCoupling

open SmoothingTree

theorem majority_bad_iff (m : ℕ) (v : Fin m → Bool) :
    majority v ≠ true ↔ (∑ i, if v i then (1 : ℝ) else 0) ≤ (m : ℝ) / 2 := by
  have he : (ones v : ℝ) = ∑ i, if v i then (1 : ℝ) else 0 := by
    simp [ones]
  simp only [majority, ne_eq, decide_eq_true_eq, not_lt]
  rw [← he]
  constructor
  · intro h
    have hh : (2 : ℝ) * ones v ≤ m := by exact_mod_cast h
    linarith
  · intro h
    have hh : (2 : ℝ) * ones v ≤ m := by linarith
    exact_mod_cast hh

theorem block_bad_eq (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) (m : ℕ) :
    probability (SmoothingNoise.block β hβ₀ hβ₁ m).law (fun v ↦ majority v ≠ true) =
      SmoothingNoise.majorityError β hβ₀ hβ₁ m := by
  simp only [probability, SmoothingNoise.majorityError, Finset.sum_filter, majority_bad_iff]

noncomputable def tapeLaw (C m : ℕ) (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    PMF (Tape C m) := pi (fun _ ↦ (SmoothingNoise.block β hβ₀ hβ₁ m).law)

theorem tapeLaw_map_block (C m : ℕ) (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2)
    (i : Fin (C + 1)) :
    (tapeLaw C m β hβ₀ hβ₁).map (Function.eval i) = (SmoothingNoise.block β hβ₀ hβ₁ m).law :=
  pi_map_eval _ i

theorem bad_tape_le (C m : ℕ) (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) (hm : 0 < m) :
    probability (tapeLaw C m β hβ₀ hβ₁) (fun tape ↦ ¬GoodTape tape) ≤
      ((C : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2) := by
  have hbad : (fun tape : Tape C m ↦ ¬GoodTape tape) =
      (fun tape ↦ ∃ i, majority (tape i) ≠ true) := by
    funext tape
    simp only [GoodTape, not_forall]
  rw [hbad]
  calc
    _ ≤ ∑ i, probability (tapeLaw C m β hβ₀ hβ₁) (fun tape ↦ majority (tape i) ≠ true) :=
      probability_exists_le _ _
    _ = ∑ _i : Fin (C + 1), SmoothingNoise.majorityError β hβ₀ hβ₁ m := by
      apply Finset.sum_congr rfl
      intro i _
      have hmap := probability_map (tapeLaw C m β hβ₀ hβ₁) (Function.eval i)
        (fun v : Fin m → Bool ↦ majority v ≠ true)
      rw [tapeLaw_map_block, block_bad_eq] at hmap
      exact hmap.symm
    _ ≤ ∑ _i : Fin (C + 1), Real.exp (-2 * (m : ℝ) * β ^ 2) :=
      Finset.sum_le_sum fun _ _ ↦ SmoothingNoise.majority_error_le β hβ₀ hβ₁ m hm
    _ = _ := by simp [Nat.cast_add, Nat.cast_one]

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R]
  [Fintype SA] [Fintype SB]

/-- An actual smoothed protocol, with a public transcript decoder and identical
decoders for Alice and Bob. This proves the fidelity/cost part of Lemma 8.4;
its smoothness and divergence-tail estimates are separate obligations. -/
theorem smoothing_simulation (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (m : ℕ) (hm : 0 < m) (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    let s := SmoothingProtocol.simulator p m (tapeLaw p.cost m β hβ₀ hβ₁)
    s.cost ≤ m * p.cost ∧
      s.Simulates μ (2 * ((p.cost : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2)) := by
  constructor
  · exact SmoothingProtocol.cost_le p m _
  · have hs := SmoothingProtocol.simulates p m (tapeLaw p.cost m β hβ₀ hβ₁) μ
    have he : 2 * SmoothingProtocol.noiseError p m (tapeLaw p.cost m β hβ₀ hβ₁) ≤
        2 * ((p.cost : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2) := by
      have hb := mul_le_mul_of_nonneg_left (bad_tape_le p.cost m β hβ₀ hβ₁ hm)
        (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [SmoothingProtocol.noiseError, mul_assoc] using hb
    exact ⟨hs.1.trans he, hs.2.trans he⟩

theorem smoothing_error_le (C m : ℕ) (β α : ℝ) (hα : 0 < α)
    (hm : Real.log (2 * ((C : ℝ) + 1) / α) ≤ 2 * (m : ℝ) * β ^ 2) :
    2 * ((C : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2) ≤ α := by
  have hC : 0 < 2 * ((C : ℝ) + 1) := by positivity
  rw [Real.log_div hC.ne' hα.ne'] at hm
  have he := Real.exp_le_exp.mpr (show Real.log (2 * ((C : ℝ) + 1)) -
      2 * (m : ℝ) * β ^ 2 ≤ Real.log α by linarith)
  rw [Real.exp_sub, Real.exp_log hC, Real.exp_log hα] at he
  simpa only [neg_mul, Real.exp_neg, div_eq_mul_inv] using he

/-- Choose a finite block size for any requested positive fidelity error.
This is the smoothing cost/fidelity construction, not the compression bound
of Theorem 2.2 and not yet the information-tail part of Lemma 8.4. -/
theorem smoothing_at_error (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β α : ℝ) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 2) (hα : 0 < α) :
    ∃ s : Simulator p,
      s.Simulates μ α ∧
      s.cost ≤ (⌈Real.log (2 * ((p.cost : ℝ) + 1) / α) / (2 * β ^ 2)⌉₊ + 1) * p.cost := by
  let m := ⌈Real.log (2 * ((p.cost : ℝ) + 1) / α) / (2 * β ^ 2)⌉₊ + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hd : 0 < 2 * β ^ 2 := by positivity
  have hc := Nat.le_ceil (Real.log (2 * ((p.cost : ℝ) + 1) / α) / (2 * β ^ 2))
  have hcm : (⌈Real.log (2 * ((p.cost : ℝ) + 1) / α) / (2 * β ^ 2)⌉₊ : ℝ) ≤ m := by
    dsimp [m]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hlog : Real.log (2 * ((p.cost : ℝ) + 1) / α) ≤ 2 * (m : ℝ) * β ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (hc.trans hcm) hd.le
    rw [div_mul_cancel₀ _ hd.ne'] at hh
    nlinarith
  obtain ⟨hcost, hs⟩ := smoothing_simulation p μ m hm β hβ.le hβ₁
  have he := smoothing_error_le p.cost m β α hα hlog
  exact ⟨_, ⟨hs.1.trans he, hs.2.trans he⟩, hcost⟩

end BBCR.SmoothingCoupling
