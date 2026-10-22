module

public import BBCR.StoppedAzuma

/-! Residual-cost potentials for finite binary kernels. An arbitrary stopping
frontier spends exactly the drop in residual expected cost. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.FiniteAzuma

theorem expect_map {A B : Type*} [Fintype A] [Fintype B]
    (p : PMF A) (f : A → B) (g : B → ℝ) : expect (p.map f) g = expect p (fun a ↦ g (f a)) :=
  Disjointness.Channel.sum_mass_map p f g

theorem expect_add {A : Type*} [Fintype A] (p : PMF A) (f g : A → ℝ) :
    expect p (fun a ↦ f a + g a) = expect p f + expect p g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_const {A : Type*} [Fintype A] (p : PMF A) (c : ℝ) : expect p (fun _ ↦ c) = c := by
  simp only [expect, ← Finset.sum_mul, sum_mass, one_mul]

end BBCR.FiniteAzuma

namespace BBCR.KernelPotential

open FiniteAzuma

noncomputable def future (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (d : List Bool → ℝ) : ℕ → List Bool → ℝ
  | 0, _ => 0
  | n + 1, s => if terminal s then 0 else d s + expect (K s) (fun b ↦ future terminal K d n (s ++ [b]))

noncomputable def value (C : ℕ) (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (d : List Bool → ℝ) (s : List Bool) : ℝ := future terminal K d (C - s.length) s

theorem value_bellman (C : ℕ) (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (d : List Bool → ℝ) (hdepth : ∀ s, C ≤ s.length → terminal s = true)
    (s : List Bool) (hs : terminal s = false) :
    value C terminal K d s = d s + expect (K s) (fun b ↦ value C terminal K d (s ++ [b])) := by
  have hlen : s.length < C := by
    by_contra hh
    have ht := hdepth s (by omega)
    simp [hs] at ht
  have hrank : C - s.length = (C - s.length - 1) + 1 := by omega
  unfold value
  rw [hrank, future, hs]
  simp only [Bool.false_eq_true, ite_false]
  congr 2
  funext b
  congr 1
  simp only [List.length_append, List.length_singleton]
  omega

theorem future_nonneg (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (d : List Bool → ℝ) (H : List Bool → Prop)
    (hchild : ∀ s, H s → terminal s = false → ∀ b, H (s ++ [b]))
    (hd : ∀ s, H s → terminal s = false → 0 ≤ d s)
    (n : ℕ) (s : List Bool) (hH : H s) : 0 ≤ future terminal K d n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hs : terminal s with
    | true => simp [future, hs]
    | false =>
      rw [future, hs]
      simp only [Bool.false_eq_true, ite_false]
      apply add_nonneg (hd s hH hs)
      exact Finset.sum_nonneg fun b _ ↦ mul_nonneg (mass_nonneg _ _) (ih _ (hchild s hH hs b))

theorem future_eq_expect (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (d : List Bool → ℝ) (n : ℕ) (s : List Bool) :
    future terminal K d n s = expect (StoppingFrontier.finiteLaw n terminal K s)
      (fun w ↦ StoppedAzuma.pathSum d s w.1) := by
  rw [← StoppedAzuma.process_finiteLaw terminal K (fun _ _ ↦ 0) (fun _ ↦ 0), expect_map]
  change future terminal K d n s = expect
    (StoppedAzuma.process terminal K (fun _ _ ↦ 0) (fun _ ↦ 0) n s).law
    (fun bits ↦ StoppedAzuma.pathSum d s (StoppedAzuma.outcome n terminal s bits))
  induction n generalizing s with
  | zero => simp [future, StoppedAzuma.outcome, StoppedAzuma.pathSum, expect]
  | succ n ih =>
    cases hs : terminal s with
    | true => simp [future, hs, StoppedAzuma.outcome, StoppedAzuma.pathSum, expect]
    | false =>
      rw [future, hs, StoppedAzuma.process, hs]
      simp only [Bool.false_eq_true, ite_false]
      rw [Process.expect_law_step]
      have he (b : Bool) : expect (StoppedAzuma.process terminal K (fun _ _ ↦ 0) (fun _ ↦ 0) n (s ++ [b])).law
          (fun bits ↦ StoppedAzuma.pathSum d s (StoppedAzuma.outcome (n + 1) terminal s (Fin.cons b bits))) =
          d s + future terminal K d n (s ++ [b]) := by
        simp only [StoppedAzuma.outcome, hs, Bool.false_eq_true, ite_false, Fin.cons_zero,
          Fin.tail_cons, StoppedAzuma.pathSum]
        rw [expect_add, expect_const, ← ih]
      simp only [he]
      rw [expect_add, expect_const]

theorem stopped_expectation (terminal halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (d V : List Bool → ℝ) (hstop : ∀ s, terminal s = true → halt s = true)
    (hbellman : ∀ s, terminal s = false → V s = d s + expect (K s) (fun b ↦ V (s ++ [b])))
    (n : ℕ) (s : List Bool) :
    expect (StoppingFrontier.finiteLaw n halt K s) (fun w ↦ StoppedAzuma.pathSum d s w.1 + V (s ++ w.1)) = V s := by
  rw [← StoppedAzuma.process_finiteLaw halt K (fun _ _ ↦ 0) (fun _ ↦ 0), expect_map]
  change expect (StoppedAzuma.process halt K (fun _ _ ↦ 0) (fun _ ↦ 0) n s).law
    (fun bits ↦ StoppedAzuma.pathSum d s (StoppedAzuma.outcome n halt s bits) +
      V (s ++ StoppedAzuma.outcome n halt s bits)) = V s
  induction n generalizing s with
  | zero => simp only [StoppedAzuma.process, StoppedAzuma.outcome, StoppedAzuma.pathSum,
      List.append_nil, zero_add]; exact expect_const _ _
  | succ n ih =>
    cases hs : halt s with
    | true =>
      have he : (fun bits ↦ StoppedAzuma.pathSum d s (StoppedAzuma.outcome (n + 1) halt s bits) +
          V (s ++ StoppedAzuma.outcome (n + 1) halt s bits)) = fun _ ↦ V s := by
        funext bits
        simp [StoppedAzuma.outcome, hs, StoppedAzuma.pathSum]
      rw [he, expect_const]
    | false =>
      have ht : terminal s = false := by
        cases ht : terminal s
        · rfl
        · have hh := hstop s ht; simp [hs] at hh
      rw [StoppedAzuma.process, hs]
      simp only [Bool.false_eq_true, ite_false]
      rw [Process.expect_law_step]
      have he (b : Bool) : expect (StoppedAzuma.process halt K (fun _ _ ↦ 0) (fun _ ↦ 0) n (s ++ [b])).law
          (fun bits ↦ StoppedAzuma.pathSum d s (StoppedAzuma.outcome (n + 1) halt s (Fin.cons b bits)) +
            V (s ++ StoppedAzuma.outcome (n + 1) halt s (Fin.cons b bits))) = d s + V (s ++ [b]) := by
        simp only [StoppedAzuma.outcome, hs, Bool.false_eq_true, ite_false, Fin.cons_zero,
          Fin.tail_cons, StoppedAzuma.pathSum]
        have hfun : (fun bits ↦ d s + StoppedAzuma.pathSum d (s ++ [b]) (StoppedAzuma.outcome n halt (s ++ [b]) bits) +
            V (s ++ b :: StoppedAzuma.outcome n halt (s ++ [b]) bits)) =
            (fun bits ↦ d s + (StoppedAzuma.pathSum d (s ++ [b]) (StoppedAzuma.outcome n halt (s ++ [b]) bits) +
              V ((s ++ [b]) ++ StoppedAzuma.outcome n halt (s ++ [b]) bits))) := by
          funext bits
          simp [List.append_assoc, add_assoc]
        rw [hfun, expect_add, expect_const, ih]
      simp only [he]
      rw [expect_add, expect_const, ← hbellman s ht]

end BBCR.KernelPotential

namespace BBCR.StoppedAzuma

theorem expect_incrementSum (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (z : List Bool → Bool → ℝ) (d : List Bool → ℝ) (H : List Bool → Prop)
    (hchild : ∀ s, H s → halt s = false → ∀ b, H (s ++ [b]))
    (hmean : ∀ s, H s → halt s = false → FiniteAzuma.expect (K s) (z s) = d s)
    (n : ℕ) (s : List Bool) (hH : H s) :
    FiniteAzuma.expect (StoppingFrontier.finiteLaw n halt K s) (fun w ↦ incrementSum z s w.1) =
      FiniteAzuma.expect (StoppingFrontier.finiteLaw n halt K s) (fun w ↦ pathSum d s w.1) := by
  have hh := (process halt K z d n s).expect_total_zero
    (process_centered halt K z d H hchild hmean n s hH)
  have he : (process halt K z d n s).total = fun bits ↦
      incrementSum z s (outcome n halt s bits) - pathSum d s (outcome n halt s bits) :=
    funext (process_total halt K z d n s)
  rw [he] at hh
  simp only [FiniteAzuma.expect, mul_sub, Finset.sum_sub_distrib, sub_eq_zero] at hh
  rw [← process_finiteLaw halt K z d, FiniteAzuma.expect_map, FiniteAzuma.expect_map]
  exact hh

end BBCR.StoppedAzuma
