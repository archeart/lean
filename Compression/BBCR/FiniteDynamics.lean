module

public import BBCR.KernelPotential

/-! Finite adaptive dynamics with a decreasing expected-cost potential.
The completion bound combines potential charging with a centered success count. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.FiniteDynamics

open FiniteAzuma

variable {S Ω : Type*} [Fintype Ω]

def stateAfter (next : S → Ω → S) : (n : ℕ) → S → (Fin n → Ω) → S
  | 0, s, _ => s
  | n + 1, s, bits => stateAfter next n (next s (bits 0)) (Fin.tail bits)

def rewardTotal (next : S → Ω → S) (g : S → Ω → ℝ) : (n : ℕ) → S → (Fin n → Ω) → ℝ
  | 0, _, _ => 0
  | n + 1, s, bits => g s (bits 0) + rewardTotal next g n (next s (bits 0)) (Fin.tail bits)

noncomputable def process (q : PMF Ω) (next : S → Ω → S) (f : S → Ω → ℝ) :
    (n : ℕ) → S → Process Ω n
  | 0, _ => .done
  | n + 1, s => .step q (f s) (-1) 1 (fun ω ↦ process q next f n (next s ω))

omit [Fintype Ω] in
theorem state_invariant (next : S → Ω → S) (H : S → Prop)
    (hnext : ∀ s, H s → ∀ ω, H (next s ω)) (n : ℕ) (s : S) (hs : H s) (bits : Fin n → Ω) :
    H (stateAfter next n s bits) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih _ (hnext s hs _) _

omit [Fintype Ω] in
theorem reward_nonneg (next : S → Ω → S) (g : S → Ω → ℝ)
    (hg : ∀ s ω, 0 ≤ g s ω) (n : ℕ) (s : S) (bits : Fin n → Ω) :
    0 ≤ rewardTotal next g n s bits := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact add_nonneg (hg _ _) (ih _ _)

omit [Fintype Ω] in
theorem rewardTotal_le (next : S → Ω → S) (f g : S → Ω → ℝ) (c : ℝ)
    (h : ∀ s ω, f s ω ≤ c + g s ω) (n : ℕ) (s : S) (bits : Fin n → Ω) :
    rewardTotal next f n s bits ≤ c * n + rewardTotal next g n s bits := by
  induction n generalizing s with
  | zero => simp [rewardTotal]
  | succ n ih =>
    simp only [rewardTotal, Nat.cast_add, Nat.cast_one]
    have hh := ih (next s (bits 0)) (Fin.tail bits)
    have hs := h s (bits 0)
    linarith

theorem expect_final (q : PMF Ω) (next : S → Ω → S) (f : S → Ω → ℝ)
    (V : S → ℝ) (H : S → Prop)
    (hnext : ∀ s, H s → ∀ ω, H (next s ω))
    (hstep : ∀ s, H s → expect q (fun ω ↦ V (next s ω)) = V s)
    (n : ℕ) (s : S) (hs : H s) :
    expect (process q next f n s).law (fun bits ↦ V (stateAfter next n s bits)) = V s := by
  induction n generalizing s with
  | zero => simp only [process, stateAfter, expect_const]
  | succ n ih =>
    rw [process, Process.expect_law_step]
    simp only [stateAfter, Fin.cons_zero, Fin.tail_cons]
    simp only [ih _ (hnext s hs _)]
    exact hstep s hs

theorem potential_budget (q : PMF Ω) (next : S → Ω → S) (f g : S → Ω → ℝ)
    (V : S → ℝ) (H : S → Prop) (a : ℝ)
    (hnext : ∀ s, H s → ∀ ω, H (next s ω))
    (hstep : ∀ s, H s → expect q (fun ω ↦ g s ω + a * V (next s ω)) ≤ a * V s)
    (n : ℕ) (s : S) (hs : H s) :
    expect (process q next f n s).law (fun bits ↦ rewardTotal next g n s bits +
      a * V (stateAfter next n s bits)) ≤ a * V s := by
  induction n generalizing s with
  | zero => simp only [process, stateAfter, rewardTotal, zero_add, expect_const, le_refl]
  | succ n ih =>
    rw [process, Process.expect_law_step]
    have he (ω : Ω) : expect (process q next f n (next s ω)).law
        (fun bits ↦ rewardTotal next g (n + 1) s (Fin.cons ω bits) +
          a * V (stateAfter next (n + 1) s (Fin.cons ω bits))) ≤ g s ω + a * V (next s ω) := by
      simp only [rewardTotal, stateAfter, Fin.cons_zero, Fin.tail_cons]
      have hf : (fun bits ↦ g s ω + rewardTotal next g n (next s ω) bits +
          a * V (stateAfter next n (next s ω) bits)) = fun bits ↦ g s ω +
          (rewardTotal next g n (next s ω) bits + a * V (stateAfter next n (next s ω) bits)) := by
        funext bits
        ring
      rw [hf, expect_add, expect_const]
      exact add_le_add le_rfl (ih _ (hnext s hs ω))
    exact (Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (he ω) (mass_nonneg q ω)).trans (hstep s hs)

theorem reward_budget (q : PMF Ω) (next : S → Ω → S) (f g : S → Ω → ℝ)
    (V : S → ℝ) (H : S → Prop) (a : ℝ) (ha : 0 ≤ a)
    (hnext : ∀ s, H s → ∀ ω, H (next s ω)) (hV : ∀ s, H s → 0 ≤ V s)
    (hstep : ∀ s, H s → expect q (fun ω ↦ g s ω + a * V (next s ω)) ≤ a * V s)
    (n : ℕ) (s : S) (hs : H s) :
    expect (process q next f n s).law (rewardTotal next g n s) ≤ a * V s := by
  apply le_trans _ (potential_budget q next f g V H a hnext hstep n s hs)
  apply Finset.sum_le_sum
  intro bits _
  apply mul_le_mul_of_nonneg_left _ (mass_nonneg _ _)
  exact le_add_of_nonneg_right (mul_nonneg ha (hV _ (state_invariant next H hnext n s hs bits)))

theorem centered (q : PMF Ω) (next : S → Ω → S) (f : S → Ω → ℝ) (H : S → Prop)
    (hnext : ∀ s, H s → ∀ ω, H (next s ω))
    (hmean : ∀ s, H s → expect q (f s) = 0)
    (hbound : ∀ s, H s → ∀ ω, f s ω ∈ Set.Icc (-1) 1)
    (n : ℕ) (s : S) (hs : H s) : (process q next f n s).Centered := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih => exact ⟨hmean s hs, hbound s hs, fun ω ↦ ih _ (hnext s hs ω)⟩

omit [Fintype Ω] in
theorem energy (q : PMF Ω) (next : S → Ω → S) (f : S → Ω → ℝ)
    (n : ℕ) (s : S) (bits : Fin n → Ω) : (process q next f n s).energy bits = 4 * n := by
  induction n generalizing s with
  | zero => simp [process, Process.energy]
  | succ n ih => simp only [process, Process.energy, ih, Nat.cast_add, Nat.cast_one]; ring

def progress (terminal : S → Bool) (next : S → Ω → S) (success : S → Ω → Bool) (s : S) (ω : Ω) : ℝ :=
  if !terminal s && success s ω && !terminal (next s ω) then 1 else 0

def centeredSuccess (terminal : S → Bool) (success : S → Ω → Bool) (ρ : ℝ) (s : S) (ω : Ω) : ℝ :=
  if terminal s then 0 else ρ - if success s ω then 1 else 0

omit [Fintype Ω] in
theorem state_after_terminal (terminal : S → Bool) (next : S → Ω → S)
    (habsorb : ∀ s, terminal s = true → ∀ ω, next s ω = s)
    (n : ℕ) (s : S) (hs : terminal s = true) (bits : Fin n → Ω) : stateAfter next n s bits = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stateAfter, habsorb s hs, ih]

omit [Fintype Ω] in
theorem unfinished_identity (q : PMF Ω) (terminal : S → Bool) (next : S → Ω → S)
    (success : S → Ω → Bool) (ρ : ℝ)
    (habsorb : ∀ s, terminal s = true → ∀ ω, next s ω = s)
    (n : ℕ) (s : S) (bits : Fin n → Ω) (hn : terminal (stateAfter next n s bits) = false) :
    (process q next (centeredSuccess terminal success ρ) n s).total bits = ρ * n -
      rewardTotal next (progress terminal next success) n s bits := by
  induction n generalizing s with
  | zero => simp [process, Process.total, rewardTotal]
  | succ n ih =>
    have hs : terminal s = false := by
      cases hs : terminal s
      · rfl
      · rw [state_after_terminal terminal next habsorb (n + 1) s hs bits, hs] at hn
        contradiction
    have ht : terminal (next s (bits 0)) = false := by
      cases ht : terminal (next s (bits 0))
      · rfl
      · change terminal (stateAfter next n (next s (bits 0)) (Fin.tail bits)) = false at hn
        rw [state_after_terminal terminal next habsorb n _ ht (Fin.tail bits), ht] at hn
        contradiction
    simp only [process, Process.total, rewardTotal]
    rw [ih _ _ hn]
    simp only [centeredSuccess, progress, hs, ht, Bool.false_eq_true, ite_false,
      Bool.not_false, Bool.true_and, Bool.and_true, Nat.cast_add, Nat.cast_one]
    ring

theorem completion_bound (q : PMF Ω) (terminal : S → Bool) (next : S → Ω → S)
    (success : S → Ω → Bool) (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (V : S → ℝ) (H : S → Prop) (a : ℝ) (ha : 0 ≤ a)
    (hnext : ∀ s, H s → ∀ ω, H (next s ω)) (hV : ∀ s, H s → 0 ≤ V s)
    (habsorb : ∀ s, terminal s = true → ∀ ω, next s ω = s)
    (hprob : ∀ s, H s → terminal s = false → expect q (fun ω ↦ if success s ω then 1 else 0) = ρ)
    (hbudget : ∀ s, H s → expect q (fun ω ↦ progress terminal next success s ω + a * V (next s ω)) ≤ a * V s)
    (n : ℕ) (hn : 0 < n) (s : S) (hs : H s) :
    probability (process q next (centeredSuccess terminal success ρ) n s).law
      (fun bits ↦ terminal (stateAfter next n s bits) = false) ≤
      2 * a * V s / (ρ * n) + Real.exp (-(ρ ^ 2 * n / 8)) := by
  let P := process q next (centeredSuccess terminal success ρ) n s
  let g := progress terminal next success
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 < ρ * n / 2 := by positivity
  have hmean (t : S) (hH : H t) : expect q (centeredSuccess terminal success ρ t) = 0 := by
    cases ht : terminal t with
    | true => simp [centeredSuccess, ht, expect]
    | false =>
      have hh := hprob t hH ht
      simp only [centeredSuccess, ht, Bool.false_eq_true, ite_false, expect, mul_sub,
        Finset.sum_sub_distrib, ← Finset.sum_mul, sum_mass, one_mul]
      exact sub_eq_zero.mpr hh.symm
  have hbound (t : S) (_ : H t) (ω : Ω) : centeredSuccess terminal success ρ t ω ∈ Set.Icc (-1) 1 := by
    cases ht : terminal t <;> cases ho : success t ω <;>
      simp only [centeredSuccess, ht, ho, Bool.false_eq_true, ite_false, ite_true, Set.mem_Icc] <;>
      constructor <;> linarith
  have hP := centered q next _ H hnext hmean hbound n s hs
  have hmarkov := probability_le_expect_div P.law (rewardTotal next g n s) (ρ * n / 2) ht
    (fun bits _ ↦ reward_nonneg next g (fun t ω ↦ by dsimp [g, progress]; split_ifs <;> norm_num) n s bits)
  have hreward := reward_budget q next (centeredSuccess terminal success ρ) g V H a ha hnext hV hbudget n s hs
  have hfirst : probability P.law (fun bits ↦ ρ * n / 2 ≤ rewardTotal next g n s bits) ≤ 2 * a * V s / (ρ * n) := by
    apply hmarkov.trans
    have hh := div_le_div_of_nonneg_right hreward ht.le
    have he : a * V s / (ρ * n / 2) = 2 * a * V s / (ρ * n) := by ring
    simpa only [expect, P] using hh.trans_eq he
  have haz := P.azuma hP (4 * n) (ρ * n / 2) (by positivity) ht.le
    (fun bits ↦ (energy q next (centeredSuccess terminal success ρ) n s bits).le)
  have hexp : -2 * (ρ * n / 2) ^ 2 / (4 * n) = -(ρ ^ 2 * n / 8) := by field_simp; ring
  rw [hexp] at haz
  have hsubset : probability P.law (fun bits ↦ terminal (stateAfter next n s bits) = false) ≤
      probability P.law (fun bits ↦ ρ * n / 2 ≤ rewardTotal next g n s bits) + P.tailMass (ρ * n / 2) := by
    have he : P.tailMass (ρ * n / 2) = probability P.law (fun bits ↦ ρ * n / 2 ≤ P.total bits) := by
      simp only [Process.tailMass, probability, Finset.sum_filter]
    rw [he]
    apply le_trans _ (probability_or_le _ _ _)
    apply probability_mono
    intro bits hb
    have hi := unfinished_identity q terminal next success ρ habsorb n s bits hb
    by_cases hh : ρ * n / 2 ≤ rewardTotal next g n s bits
    · exact Or.inl hh
    · exact Or.inr (by dsimp only [P]; dsimp only [g] at hh; linarith)
  exact hsubset.trans (add_le_add hfirst haz)

end BBCR.FiniteDynamics
