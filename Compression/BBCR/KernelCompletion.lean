module

public import BBCR.KernelPotential

/-! Terminal payoffs of a finite binary kernel are harmonic before termination.
This supplies the output-law invariant for exact adaptive frontier sampling. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.KernelCompletion

open FiniteAzuma

noncomputable def future (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (f : List Bool → ℝ) : ℕ → List Bool → ℝ
  | 0, s => f s
  | n + 1, s => if terminal s then f s else expect (K s) (fun b ↦ future terminal K f n (s ++ [b]))

noncomputable def value (C : ℕ) (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (f : List Bool → ℝ) (s : List Bool) : ℝ := future terminal K f (C - s.length) s

theorem value_terminal (C : ℕ) (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (f : List Bool → ℝ) (s : List Bool) (hs : terminal s = true) : value C terminal K f s = f s := by
  unfold value
  cases C - s.length <;> simp [future, hs]

theorem value_bellman (C : ℕ) (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (f : List Bool → ℝ) (hdepth : ∀ s, C ≤ s.length → terminal s = true)
    (s : List Bool) (hs : terminal s = false) :
    value C terminal K f s = expect (K s) (fun b ↦ value C terminal K f (s ++ [b])) := by
  have hlen : s.length < C := by
    by_contra hh
    have ht := hdepth s (by omega)
    simp [hs] at ht
  have hrank : C - s.length = (C - s.length - 1) + 1 := by omega
  unfold value
  rw [hrank, future, hs]
  simp only [Bool.false_eq_true, ite_false]
  congr 1
  funext b
  congr 1
  simp only [List.length_append, List.length_singleton]
  omega

theorem future_nonneg (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (f : List Bool → ℝ) (hf : ∀ s, 0 ≤ f s) (n : ℕ) (s : List Bool) :
    0 ≤ future terminal K f n s := by
  induction n generalizing s with
  | zero => exact hf s
  | succ n ih =>
    rw [future]
    split_ifs
    · exact hf s
    · exact Finset.sum_nonneg fun b _ ↦ mul_nonneg (mass_nonneg _ _) (ih _)

theorem future_eq_expect (terminal : List Bool → Bool) (K : List Bool → PMF Bool)
    (f : List Bool → ℝ) (n : ℕ) (s : List Bool) :
    future terminal K f n s = expect (StoppingFrontier.finiteLaw n terminal K s)
      (fun w ↦ f (s ++ w.1)) := by
  rw [← StoppedAzuma.process_finiteLaw terminal K (fun _ _ ↦ 0) (fun _ ↦ 0), expect_map]
  change future terminal K f n s = expect
    (StoppedAzuma.process terminal K (fun _ _ ↦ 0) (fun _ ↦ 0) n s).law
    (fun bits ↦ f (s ++ StoppedAzuma.outcome n terminal s bits))
  induction n generalizing s with
  | zero => simp [future, StoppedAzuma.outcome, expect_const]
  | succ n ih =>
    cases hs : terminal s with
    | true => simp [future, hs, StoppedAzuma.outcome, expect_const]
    | false =>
      rw [future, hs, StoppedAzuma.process, hs]
      simp only [Bool.false_eq_true, ite_false]
      rw [Process.expect_law_step]
      have he (b : Bool) : expect (StoppedAzuma.process terminal K (fun _ _ ↦ 0) (fun _ ↦ 0) n (s ++ [b])).law
          (fun bits ↦ f (s ++ StoppedAzuma.outcome (n + 1) terminal s (Fin.cons b bits))) =
          future terminal K f n (s ++ [b]) := by
        simp only [StoppedAzuma.outcome, hs, Bool.false_eq_true, ite_false, Fin.cons_zero,
          Fin.tail_cons]
        simpa only [List.append_assoc, List.singleton_append] using (ih (s ++ [b])).symm
      simp only [he]

theorem frontier_harmonic (C : ℕ) (terminal halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (f : List Bool → ℝ) (hstop : ∀ s, terminal s = true → halt s = true)
    (hdepth : ∀ s, C ≤ s.length → terminal s = true) (n : ℕ) (s : List Bool) :
    expect (StoppingFrontier.finiteLaw n halt K s)
      (fun w ↦ value C terminal K f (s ++ w.1)) = value C terminal K f s := by
  have hh := KernelPotential.stopped_expectation terminal halt K (fun _ ↦ 0)
    (value C terminal K f) hstop
    (fun t ht ↦ by simpa only [zero_add] using value_bellman C terminal K f hdepth t ht) n s
  have hz (s w : List Bool) : StoppedAzuma.pathSum (fun _ ↦ 0) s w = 0 := by
    induction w generalizing s with
    | nil => rfl
    | cons b w ih => simp only [StoppedAzuma.pathSum, ih, zero_add]
  simpa only [hz, zero_add] using hh

end BBCR.KernelCompletion
