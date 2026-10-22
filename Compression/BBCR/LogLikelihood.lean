module

public import BBCR.SmallInformation
public import BBCR.SmoothDivergence
public import BBCR.FiniteAzuma

/-! The local analytic estimate used in BBCR Claim 8.9. Natural logarithms
are used throughout: the squared range is at most 64 times local KL. -/

@[expose] public section

open Disjointness Disjointness.Hellinger

namespace BBCR

theorem abs_log_sub_le_four (a b : ℝ) (ha : 1 / 4 ≤ a) (hb : 1 / 4 ≤ b) :
    |Real.log a - Real.log b| ≤ 4 * |a - b| := by
  have haux (a b : ℝ) (ha : 1 / 4 ≤ a) (hab : a ≤ b) :
      Real.log b - Real.log a ≤ 4 * (b - a) := by
    have ha₀ : 0 < a := by linarith
    have hb₀ : 0 < b := ha₀.trans_le hab
    have hlog := Real.log_le_sub_one_of_pos (div_pos hb₀ ha₀)
    rw [Real.log_div hb₀.ne' ha₀.ne'] at hlog
    have hrat : b / a - 1 ≤ 4 * (b - a) := by
      rw [show b / a - 1 = (b - a) / a by field_simp]
      apply (div_le_iff₀ ha₀).mpr
      nlinarith
    exact hlog.trans hrat
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab),
      abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log (by linarith) hab))]
    linarith [haux a b ha hab]
  · rw [abs_of_nonneg (sub_nonneg.mpr hba),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) hba))]
    exact haux b a hb hba

theorem variation_bool (p q : PMF Bool) :
    variation p q = |mass p true - mass q true| := by
  have hp := sum_mass p
  have hq := sum_mass q
  simp only [Fintype.sum_bool] at hp hq
  have he : mass p false - mass q false = -(mass p true - mass q true) := by linarith
  simp only [variation, Fintype.sum_bool, he, abs_neg]
  ring

noncomputable def logIncrement (p q : PMF Bool) (b : Bool) : ℝ :=
  Real.log (mass p b / mass q b)

theorem expect_logIncrement (p q : PMF Bool) :
    FiniteAzuma.expect p (logIncrement p q) = divergence p q := rfl

theorem logIncrement_width_sq (p q : PMF Bool)
    (hp : ∀ b, 1 / 4 ≤ mass p b) (hq : ∀ b, 1 / 4 ≤ mass q b) :
    (max (logIncrement p q false) (logIncrement p q true) -
      min (logIncrement p q false) (logIncrement p q true)) ^ 2 ≤
        64 * divergence p q := by
  have hex (b : Bool) : logIncrement p q b = Real.log (mass p b) - Real.log (mass q b) :=
    Real.log_div (by linarith [hp b]) (by linarith [hq b])
  have hpSum := sum_mass p
  have hqSum := sum_mass q
  simp only [Fintype.sum_bool] at hpSum hqSum
  have hgap : |mass p false - mass q false| = |mass p true - mass q true| := by
    rw [show mass p false - mass q false = -(mass p true - mass q true) by linarith, abs_neg]
  have ht := abs_log_sub_le_four _ _ (hp true) (hq true)
  have hf := abs_log_sub_le_four _ _ (hp false) (hq false)
  have htri := abs_sub (Real.log (mass p false) - Real.log (mass q false))
    (Real.log (mass p true) - Real.log (mass q true))
  have hwidth : |logIncrement p q false - logIncrement p q true| ≤
      8 * |mass p true - mass q true| := by
    rw [hex false, hex true]
    rw [hgap] at hf
    linarith
  have hkl := variation_sq_le_divergence p q (fun b hz ↦ by linarith [hq b])
  rw [variation_bool] at hkl
  have hw : max (logIncrement p q false) (logIncrement p q true) -
      min (logIncrement p q false) (logIncrement p q true) =
      |logIncrement p q false - logIncrement p q true| := by
    rcases le_total (logIncrement p q false) (logIncrement p q true) with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
  rw [hw]
  nlinarith [abs_nonneg (logIncrement p q false - logIncrement p q true),
    abs_nonneg (mass p true - mass q true)]

end BBCR
