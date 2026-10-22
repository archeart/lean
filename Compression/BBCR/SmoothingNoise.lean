module

public import BBCR.FiniteAzuma

/-! The independent biased-noise block used to smooth one communicated bit.
The whole-protocol coupling and divergence-tail argument are not proved here. -/

@[expose] public section

open Real Disjointness.Hellinger BBCR.FiniteAzuma

namespace BBCR.FiniteAzuma.Process

variable {A : Type*} [Fintype A]

def iid (p : PMF A) (f : A → ℝ) (lo hi : ℝ) : (n : ℕ) → Process A n
  | 0 => .done
  | n + 1 => .step p f lo hi (fun _ ↦ iid p f lo hi n)

theorem iid_centered (p : PMF A) (f : A → ℝ) (lo hi : ℝ)
    (hmean : expect p f = 0) (hbound : ∀ x, f x ∈ Set.Icc lo hi) (n : ℕ) :
    (iid p f lo hi n).Centered := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hmean, hbound, fun _ ↦ ih⟩

omit [Fintype A] in
theorem iid_total (p : PMF A) (f : A → ℝ) (lo hi : ℝ)
    (n : ℕ) (path : Fin n → A) :
    (iid p f lo hi n).total path = ∑ i, f (path i) := by
  induction n with
  | zero => simp [iid, total]
  | succ n ih => simp [iid, total, ih, Fin.sum_univ_succ, Fin.tail]

omit [Fintype A] in
theorem iid_energy (p : PMF A) (f : A → ℝ) (lo hi : ℝ)
    (n : ℕ) (path : Fin n → A) :
    (iid p f lo hi n).energy path = (n : ℝ) * (hi - lo) ^ 2 := by
  induction n with
  | zero => simp [iid, energy]
  | succ n ih => simp only [iid, energy, ih, Nat.cast_add, Nat.cast_one]; ring

end BBCR.FiniteAzuma.Process

namespace BBCR.SmoothingNoise

/-- `true` means the transmitted noisy bit agrees with the intended bit.
This correctness law does not depend on the intended bit's value. -/
noncomputable def coin (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) : PMF Bool :=
  PMF.ofFintype (fun b ↦ if b then ENNReal.ofReal (1 / 2 + β)
    else ENNReal.ofReal (1 / 2 - β)) (by
    simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    norm_num)

@[simp] theorem coin_true (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    mass (coin β hβ₀ hβ₁) true = 1 / 2 + β :=
  ENNReal.toReal_ofReal (by linarith)

@[simp] theorem coin_false (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    mass (coin β hβ₀ hβ₁) false = 1 / 2 - β :=
  ENNReal.toReal_ofReal (by linarith)

noncomputable def score (β : ℝ) (b : Bool) : ℝ := (1 / 2 + β) - if b then 1 else 0

theorem score_mean (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) :
    expect (coin β hβ₀ hβ₁) (score β) = 0 := by
  simp only [expect, Fintype.sum_bool, coin_true, coin_false, score,
    Bool.false_eq_true, ite_false, ite_true]
  ring

theorem score_bounded (β : ℝ) (b : Bool) : score β b ∈ Set.Icc (β - 1 / 2) (β + 1 / 2) := by
  cases b <;> simp [score, Set.mem_Icc] <;> constructor <;> linarith

noncomputable def block (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) (n : ℕ) : Process Bool n :=
  Process.iid (coin β hβ₀ hβ₁) (score β) (β - 1 / 2) (β + 1 / 2) n

theorem block_centered (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) (n : ℕ) :
    (block β hβ₀ hβ₁ n).Centered :=
  Process.iid_centered _ _ _ _ (score_mean β hβ₀ hβ₁) (score_bounded β) n

theorem block_total (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) (n : ℕ) (path : Fin n → Bool) :
    (block β hβ₀ hβ₁ n).total path =
      (n : ℝ) * (1 / 2 + β) - ∑ i, if path i then (1 : ℝ) else 0 := by
  rw [block, Process.iid_total]
  simp [score, Finset.sum_sub_distrib]
  ring

theorem block_energy (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) (n : ℕ) (path : Fin n → Bool) :
    (block β hβ₀ hβ₁ n).energy path = (n : ℝ) := by
  rw [block, Process.iid_energy]
  ring

noncomputable def majorityError (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) (n : ℕ) : ℝ :=
  ∑ path ∈ Finset.univ.filter (fun path : Fin n → Bool ↦
    (∑ i, if path i then (1 : ℝ) else 0) ≤ (n : ℝ) / 2), mass (block β hβ₀ hβ₁ n).law path

/-- The probability that a noisy block has at most half correct bits is at most
`exp(-2 n β²)`. This also bounds a majority decoder that treats ties as errors. -/
theorem majority_error_le (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) (n : ℕ) (hn : 0 < n) :
    majorityError β hβ₀ hβ₁ n ≤ Real.exp (-2 * (n : ℝ) * β ^ 2) := by
  classical
  have h := (block β hβ₀ hβ₁ n).azuma (block_centered β hβ₀ hβ₁ n)
    (n : ℝ) ((n : ℝ) * β) (by exact_mod_cast hn) (mul_nonneg (Nat.cast_nonneg _) hβ₀)
    (fun path ↦ (block_energy β hβ₀ hβ₁ n path).le)
  have he : majorityError β hβ₀ hβ₁ n = (block β hβ₀ hβ₁ n).tailMass ((n : ℝ) * β) := by
    unfold majorityError Process.tailMass
    congr 1
    ext path
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, block_total]
    constructor <;> intro hh <;> linarith
  rw [he]
  have hexp : -2 * ((n : ℝ) * β) ^ 2 / (n : ℝ) = -2 * (n : ℝ) * β ^ 2 := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rwa [hexp] at h

end BBCR.SmoothingNoise
