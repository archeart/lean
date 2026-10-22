module

public import BBCR.StoppedAzuma
public import BBCR.LogLikelihood

/-! Logarithms of stopped likelihood ratios are sums of the corresponding
local increments. The positivity hypotheses are propagated, not assumed for
the resulting frontier distributions. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.StoppedAzuma

theorem law_logRatio (halt : List Bool → Bool) (P C : List Bool → PMF Bool)
    (H : List Bool → Prop)
    (hchild : ∀ s, H s → halt s = false → ∀ b, H (s ++ [b]))
    (hpos : ∀ s, H s → halt s = false → ∀ b, 0 < mass (P s) b ∧ 0 < mass (C s) b)
    (n : ℕ) (s w : List Bool) (hH : H s) (hw : w ∈ StoppingFrontier.paths n halt s) :
    0 < mass (StoppingFrontier.law n halt P s) w ∧
      0 < mass (StoppingFrontier.law n halt C s) w ∧
      Real.log (mass (StoppingFrontier.law n halt P s) w /
        mass (StoppingFrontier.law n halt C s) w) = incrementSum (fun s ↦ logIncrement (P s) (C s)) s w := by
  induction n generalizing s w with
  | zero =>
    have he : w = [] := by simpa [StoppingFrontier.paths] using hw
    subst w
    simp [StoppingFrontier.law, mass, incrementSum]
  | succ n ih =>
    cases hs : halt s with
    | true =>
      have he : w = [] := by simpa [StoppingFrontier.paths, hs] using hw
      subst w
      simp [StoppingFrontier.law, hs, mass, incrementSum]
    | false =>
      cases w with
      | nil => simp [StoppingFrontier.paths, hs] at hw
      | cons b w =>
        have hc : w ∈ StoppingFrontier.paths n halt (s ++ [b]) := by
          cases b <;> simpa [StoppingFrontier.paths, hs] using hw
        obtain ⟨hP,hC,he⟩ := ih (s ++ [b]) w (hchild s hH hs b) hc
        obtain ⟨hp,hc⟩ := hpos s hH hs b
        simp only [StoppingFrontier.mass_law_cons, hs, Bool.false_eq_true, ite_false]
        refine ⟨mul_pos hp hP, mul_pos hc hC, ?_⟩
        rw [Real.log_div (mul_pos hp hP).ne' (mul_pos hc hC).ne',
          Real.log_mul hp.ne' hP.ne', Real.log_mul hc.ne' hC.ne']
        rw [Real.log_div hP.ne' hC.ne'] at he
        simp only [incrementSum, logIncrement, Real.log_div hp.ne' hc.ne']
        linarith

theorem logRatio_tail (halt : List Bool → Bool) (K P C : List Bool → PMF Bool)
    (d : List Bool → ℝ) (H : List Bool → Prop)
    (hchild : ∀ s, H s → halt s = false → ∀ b, H (s ++ [b]))
    (hpos : ∀ s, H s → halt s = false → ∀ b, 0 < mass (P s) b ∧ 0 < mass (C s) b)
    (hmean : ∀ s, H s → halt s = false →
      FiniteAzuma.expect (K s) (logIncrement (P s) (C s)) = d s)
    (a : ℝ) (ha : 0 ≤ a)
    (hwidth : ∀ s, H s → halt s = false →
      (max (logIncrement (P s) (C s) false) (logIncrement (P s) (C s) true) -
        min (logIncrement (P s) (C s) false) (logIncrement (P s) (C s) true)) ^ 2 ≤ a * d s)
    (n : ℕ) (s : List Bool) (hH : H s) (B c t : ℝ) (hc : 0 < c) (ht : B ≤ t)
    (hB : ∀ w ∈ StoppingFrontier.paths n halt s, pathSum d s w ≤ B)
    (hBc : a * B ≤ c) :
    probability (StoppingFrontier.finiteLaw n halt K s) (fun w ↦ t ≤
      Real.log (mass (StoppingFrontier.finiteLaw n halt P s) w /
        mass (StoppingFrontier.finiteLaw n halt C s) w)) ≤ Real.exp (-2 * (t - B) ^ 2 / c) := by
  have he (w : ↥(StoppingFrontier.paths n halt s)) :
      Real.log (mass (StoppingFrontier.finiteLaw n halt P s) w /
        mass (StoppingFrontier.finiteLaw n halt C s) w) =
          incrementSum (fun s ↦ logIncrement (P s) (C s)) s w.1 :=
    (law_logRatio halt P C H hchild hpos n s w.1 hH w.2).2.2
  simp_rw [he]
  exact increment_tail halt K (fun s ↦ logIncrement (P s) (C s)) d H hchild hmean
    a ha hwidth n s hH B c t hc ht hB hBc

end BBCR.StoppedAzuma
