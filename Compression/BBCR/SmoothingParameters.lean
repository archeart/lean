module

public import BBCR.SmoothingTail
public import BBCR.SmallInformation

/-! Explicit smoothing parameters absorb the bad-noise information correction.
The logarithmic block-length estimates are separate from the still-open smooth
compression construction. -/

@[expose] public section

open Disjointness Disjointness.Hellinger

namespace BBCR.SmoothingCoupling

noncomputable def informationLog (C : ℕ) (α β : ℝ) : ℝ :=
  Real.log (2 * ((C : ℝ) + 1) ^ 2 / (α ^ 2 * β ^ 2))

noncomputable def informationBlockSize (C : ℕ) (α β : ℝ) : ℕ :=
  ⌈informationLog C α β / β ^ 2⌉₊ + 1

theorem informationBlockSize_pos (C : ℕ) (α β : ℝ) :
    0 < informationBlockSize C α β := by
  unfold informationBlockSize
  omega

theorem informationLog_nonneg (C : ℕ) (α β : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 2) :
    0 ≤ informationLog C α β := by
  have ha : α ^ 2 ≤ 1 := by nlinarith
  have hb : β ^ 2 ≤ 1 := by nlinarith
  have hd : α ^ 2 * β ^ 2 ≤ 1 := by nlinarith [sq_nonneg α, sq_nonneg β]
  apply Real.log_nonneg
  apply (le_div_iff₀ (by positivity : 0 < α ^ 2 * β ^ 2)).mpr
  have hC : 0 ≤ (C : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem informationBlockSize_lower (C : ℕ) (α β : ℝ) (hβ : 0 < β) :
    informationLog C α β ≤ (informationBlockSize C α β : ℝ) * β ^ 2 := by
  have hc := Nat.le_ceil (informationLog C α β / β ^ 2)
  have hm : (⌈informationLog C α β / β ^ 2⌉₊ : ℝ) ≤ informationBlockSize C α β := by
    simp only [informationBlockSize, Nat.cast_add, Nat.cast_one]
    linarith
  exact (div_le_iff₀ (sq_pos_of_pos hβ)).mp (hc.trans hm)

/-- Only logarithmic dependence on the stronger requested noise accuracy. -/
theorem informationBlockSize_upper (C : ℕ) (α β : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 2) :
    (informationBlockSize C α β : ℝ) ≤ informationLog C α β / β ^ 2 + 2 := by
  have hc := Nat.ceil_lt_add_one (div_nonneg
    (informationLog_nonneg C α β hα hα₁ hβ hβ₁) (sq_nonneg β))
  simp only [informationBlockSize, Nat.cast_add, Nat.cast_one]
  linarith

theorem informationLog_eq (C : ℕ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    informationLog C α β = Real.log 2 + 2 * Real.log (((C : ℝ) + 1) / (α * β)) := by
  have hC : (C : ℝ) + 1 ≠ 0 := by positivity
  have he : 2 * ((C : ℝ) + 1) ^ 2 / (α ^ 2 * β ^ 2) =
      2 * (((C : ℝ) + 1) / (α * β)) ^ 2 := by field_simp
  rw [informationLog, he, Real.log_mul (by norm_num)
    (pow_ne_zero 2 (div_ne_zero hC (mul_ne_zero hα.ne' hβ.ne'))), Real.log_pow]
  norm_num

/-- The stronger information accuracy still requires only a logarithmic number
of repetitions beyond the inverse-square bias factor. -/
theorem informationBlockSize_log_bound (C : ℕ) (α β : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 2) :
    (informationBlockSize C α β : ℝ) ≤
      (3 * Real.log (((C : ℝ) + 1) / (α * β)) + 2) / β ^ 2 := by
  have hprod : α * β ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hα₁ hβ.le).trans (by simpa using hβ₁)
  have htwo : 2 ≤ ((C : ℝ) + 1) / (α * β) := by
    apply (le_div_iff₀ (mul_pos hα hβ)).mpr
    nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo
  have hL : informationLog C α β ≤ 3 * Real.log (((C : ℝ) + 1) / (α * β)) := by
    rw [informationLog_eq C α β hα hβ]
    linarith
  have hb : β ^ 2 ≤ 1 := by nlinarith
  have hu := mul_le_mul_of_nonneg_right
    (informationBlockSize_upper C α β hα hα₁ hβ hβ₁) (sq_nonneg β)
  rw [add_mul, div_mul_cancel₀ _ (sq_pos_of_pos hβ).ne'] at hu
  apply (le_div_iff₀ (sq_pos_of_pos hβ)).mpr
  nlinarith

theorem exp_neg_informationLog (C : ℕ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Real.exp (-informationLog C α β) = α ^ 2 * β ^ 2 / (2 * ((C : ℝ) + 1) ^ 2) := by
  rw [informationLog, Real.exp_neg, Real.exp_log (by positivity)]
  rw [inv_div]

/-- Splitting the exponent absorbs the linear block-length multiplier. -/
theorem mul_exp_neg_two_le (x : ℝ) : x * Real.exp (-2 * x) ≤ Real.exp (-x) := by
  have hx : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  calc
    _ ≤ Real.exp x * Real.exp (-2 * x) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The same explicit block size makes both transcript error and the additive
information correction small. This includes zero-communication originals. -/
theorem informationBlockSize_bounds (C : ℕ) (α β : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 2) :
    let m := informationBlockSize C α β
    (2 * ((C : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2) ≤ α) ∧
      (2 * ((C : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2)) *
        ((m * C : ℕ) : ℝ) * Real.log 2 ≤ α ^ 2 := by
  let m := informationBlockSize C α β
  let x := (m : ℝ) * β ^ 2
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hL : informationLog C α β ≤ x := informationBlockSize_lower C α β hβ
  have he : Real.exp (-x) ≤ α ^ 2 * β ^ 2 / (2 * ((C : ℝ) + 1) ^ 2) := by
    rw [← exp_neg_informationLog C α β hα hβ]
    exact Real.exp_le_exp.mpr (neg_le_neg hL)
  have htwo : Real.exp (-2 * x) ≤ Real.exp (-x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hC : 0 ≤ (C : ℝ) := Nat.cast_nonneg _
  have hC₁ : 0 < (C : ℝ) + 1 := by positivity
  have hb : β ^ 2 ≤ 1 := by nlinarith
  have ha : α ^ 2 ≤ α := by nlinarith
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlog₀ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hprod : (C : ℝ) * Real.log 2 ≤ (C : ℝ) + 1 := by nlinarith
  constructor
  · change 2 * ((C : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2) ≤ α
    have hh := mul_le_mul_of_nonneg_left (htwo.trans he) (by positivity : 0 ≤ 2 * ((C : ℝ) + 1))
    have hn : 2 * ((C : ℝ) + 1) *
        (α ^ 2 * β ^ 2 / (2 * ((C : ℝ) + 1) ^ 2)) ≤ α := by
      have hid : 2 * ((C : ℝ) + 1) * (α ^ 2 * β ^ 2 / (2 * ((C : ℝ) + 1) ^ 2)) =
          α ^ 2 * β ^ 2 / ((C : ℝ) + 1) := by field_simp
      rw [hid]
      apply (div_le_iff₀ hC₁).mpr
      have hab := (mul_le_mul_of_nonneg_left hb (sq_nonneg α)).trans_eq (mul_one _)
      nlinarith
    have hscale : -2 * (m : ℝ) * β ^ 2 = -2 * x := by dsimp only [x]; ring
    rw [hscale]
    exact hh.trans hn
  · change (2 * ((C : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2)) *
        ((m * C : ℕ) : ℝ) * Real.log 2 ≤ α ^ 2
    have hh := (mul_exp_neg_two_le x).trans he
    have hf : 0 ≤ 2 * ((C : ℝ) + 1) * C * Real.log 2 / β ^ 2 := by positivity
    have hm := mul_le_mul_of_nonneg_left hh hf
    have hid : (2 * ((C : ℝ) + 1) * C * Real.log 2 / β ^ 2) *
        (x * Real.exp (-2 * x)) =
        (2 * ((C : ℝ) + 1) * Real.exp (-2 * (m : ℝ) * β ^ 2)) *
          ((m * C : ℕ) : ℝ) * Real.log 2 := by
      dsimp only [x]
      push_cast
      field_simp
    rw [hid] at hm
    refine hm.trans ?_
    have hid' : (2 * ((C : ℝ) + 1) * C * Real.log 2 / β ^ 2) *
        (α ^ 2 * β ^ 2 / (2 * ((C : ℝ) + 1) ^ 2)) =
        α ^ 2 * ((C : ℝ) * Real.log 2 / ((C : ℝ) + 1)) := by
      field_simp
    rw [hid']
    exact (mul_le_mul_of_nonneg_left ((div_le_one hC₁).mpr hprod) (sq_nonneg α)).trans_eq
      (mul_one _)

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R]
  [Fintype SA] [Fintype SB]

noncomputable def informationSimulator (p : Protocol X Y R SA SB) (α β : ℝ)
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 2) : Simulator p :=
  let m := informationBlockSize p.cost α β
  SmoothingProtocol.simulator p m (tapeLaw p.cost m β hβ₀ hβ₁)

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

/-- Explicit smoothing with requested error and additive information increase
at most the square of that error, for the same actual simulator. -/
theorem smoothing_at_information_error (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (α β : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 2) :
    let s := informationSimulator p α β hβ.le hβ₁
    s.cost ≤ informationBlockSize p.cost α β * p.cost ∧
      s.Simulates μ α ∧ Smooth s.protocol β ∧
      externalInformation s.protocol μ ≤ externalInformation p μ + α ^ 2 := by
  let m := informationBlockSize p.cost α β
  obtain ⟨hc,hs,hsm,hi⟩ := smoothing_with_information p μ m
    (informationBlockSize_pos _ _ _) β hβ.le hβ₁
  obtain ⟨he,hcorr⟩ := informationBlockSize_bounds p.cost α β hα hα₁ hβ hβ₁
  exact ⟨hc,⟨hs.1.trans he,hs.2.trans he⟩,hsm,hi.trans (add_le_add le_rfl hcorr)⟩

omit [Fintype X] [Fintype Y]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem informationSimulator_cost_le (p : Protocol X Y R SA SB)
    (α β : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 2) :
    let s := informationSimulator p α β hβ.le hβ₁
    (s.cost : ℝ) ≤
      ((3 * Real.log (((p.cost : ℝ) + 1) / (α * β)) + 2) / β ^ 2) * p.cost := by
  have hc := SmoothingProtocol.cost_le p (informationBlockSize p.cost α β)
    (tapeLaw p.cost (informationBlockSize p.cost α β) β hβ.le hβ₁)
  have hc' : ((informationSimulator p α β hβ.le hβ₁).cost : ℝ) ≤
      (informationBlockSize p.cost α β : ℝ) * p.cost := by exact_mod_cast hc
  exact hc'.trans (mul_le_mul_of_nonneg_right
    (informationBlockSize_log_bound p.cost α β hα hα₁ hβ hβ₁) (Nat.cast_nonneg _))

/-- Outside the already-solved small-information regime the smoothed protocol
has at most twice the original information. -/
theorem smoothing_information_le_twice (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (α β : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 2)
    (hinfo : α ^ 2 ≤ externalInformation p μ) :
    externalInformation (informationSimulator p α β hβ.le hβ₁).protocol μ ≤
      2 * externalInformation p μ := by
  have hi := (smoothing_at_information_error p μ α β hα hα₁ hβ hβ₁).2.2.2
  linarith

/-- An original-information tail estimate with no remaining additive noise
term, in the non-small-information regime. -/
theorem smoothing_tail_at_information (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (α β : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 2)
    (hinfo : α ^ 2 ≤ externalInformation p μ) :
    let q := (informationSimulator p α β hβ.le hβ₁).protocol
    (∑ r, mass q.publicLaw r * probability (Prefix.Prior.execution q μ)
      (fun ω ↦ 2 * externalInformation p μ / α ≤
        Prefix.Prior.pathDivergence q μ r q.cost ω)) ≤ α := by
  have hI : 0 < externalInformation p μ := (sq_pos_of_pos hα).trans_le hinfo
  have ht : 0 < 2 * externalInformation p μ / α := by positivity
  let m := informationBlockSize p.cost α β
  let q := SmoothingProtocol.protocol p m (tapeLaw p.cost m β hβ.le hβ₁)
  have hh := (divergence_tail_le q μ _ ht).trans
    (div_le_div_of_nonneg_right
      (smoothing_information_le_twice p μ α β hα hα₁ hβ hβ₁ hinfo) ht.le)
  have he : 2 * externalInformation p μ / (2 * externalInformation p μ / α) = α := by
    field_simp
  rwa [he] at hh

/-- Every original protocol is either already simulable with zero communication
or admits the concrete smooth simulation with information at most twice the
original. No positive-information hypothesis is hidden in the construction. -/
theorem small_or_information_smoothing (p : Protocol X Y R SA SB) (μ : PMF (X × Y))
    (α β : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) (hβ : 0 < β) (hβ₁ : β ≤ 1 / 2) :
    (∃ s : Simulator p, s.cost = 0 ∧ s.Simulates μ α) ∨
      (let s := informationSimulator p α β hβ.le hβ₁
       s.cost ≤ informationBlockSize p.cost α β * p.cost ∧
         s.Simulates μ α ∧ Smooth s.protocol β ∧
         externalInformation s.protocol μ ≤ 2 * externalInformation p μ) := by
  by_cases hinfo : externalInformation p μ ≤ α ^ 2
  · exact Or.inl (small_information_compression p μ α hα.le hinfo)
  · right
    have hI : α ^ 2 ≤ externalInformation p μ := (lt_of_not_ge hinfo).le
    obtain ⟨hc,hs,hsm,_⟩ := smoothing_at_information_error p μ α β hα hα₁ hβ hβ₁
    exact ⟨hc,hs,hsm,smoothing_information_le_twice p μ α β hα hα₁ hβ hβ₁ hI⟩

end BBCR.SmoothingCoupling
