module

public import BBCR.Concentration
public import Disjointness.BinaryInformation

/-! A finite branching-process proof of the predictable-width version of Azuma.
Widths may depend on the entire history, and only their pathwise squared sum is
bounded. No deterministic bound for each time step is substituted. -/

@[expose] public section

open Real Disjointness Disjointness.Hellinger

namespace BBCR.FiniteAzuma

variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def expect (p : PMF A) (f : A → ℝ) : ℝ := ∑ x, mass p x * f x

theorem expect_bind (p : PMF A) (K : A → PMF B) (f : B → ℝ) :
    expect (p.bind K) f = expect p (fun x ↦ expect (K x) f) := by
  simp only [expect, Disjointness.Channel.mass_bind, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro y _
  ring

inductive Process (A : Type*) : ℕ → Type _ where
  | done : Process A 0
  | step {n : ℕ} (p : PMF A) (f : A → ℝ) (lo hi : ℝ)
      (next : A → Process A n) : Process A (n + 1)

namespace Process

def Centered : {n : ℕ} → Process A n → Prop
  | _, .done => True
  | _, .step p f lo hi next =>
      expect p f = 0 ∧ (∀ x, f x ∈ Set.Icc lo hi) ∧ ∀ x, (next x).Centered

noncomputable def law : {n : ℕ} → Process A n → PMF (Fin n → A)
  | _, .done => PMF.pure Fin.elim0
  | _, .step p _ _ _ next => p.bind fun x ↦ (next x).law.map (Fin.cons x)

def total : {n : ℕ} → Process A n → (Fin n → A) → ℝ
  | _, .done, _ => 0
  | _, .step _ f _ _ next, path => f (path 0) + (next (path 0)).total (Fin.tail path)

def energy : {n : ℕ} → Process A n → (Fin n → A) → ℝ
  | _, .done, _ => 0
  | _, .step _ _ lo hi next, path =>
      (hi - lo) ^ 2 + (next (path 0)).energy (Fin.tail path)

theorem expect_law_step {n : ℕ} (p : PMF A) (f : A → ℝ) (lo hi : ℝ)
    (next : A → Process A n) (g : (Fin (n + 1) → A) → ℝ) :
    expect (Process.step p f lo hi next).law g =
      expect p (fun x ↦ expect (next x).law (fun path ↦ g (Fin.cons x path))) := by
  rw [law, expect_bind]
  unfold expect
  congr 1
  funext x
  dsimp only
  rw [Disjointness.Channel.sum_mass_map]

theorem expect_total_zero {n : ℕ} (P : Process A n) (hP : P.Centered) :
    expect P.law P.total = 0 := by
  induction P with
  | done => simp [law, total, expect]
  | step p f lo hi next ih =>
    rw [expect_law_step]
    have he (x : A) : expect (next x).law (fun path ↦
        (Process.step p f lo hi next).total (Fin.cons x path)) = f x := by
      simp only [total, Fin.cons_zero, Fin.tail_cons, expect, mul_add, Finset.sum_add_distrib,
        ← Finset.sum_mul, sum_mass, one_mul]
      rw [show (∑ path, mass (next x).law path * (next x).total path) = 0 from ih x (hP.2.2 x), add_zero]
    simp only [he]
    exact hP.1

/-- The exponential potential is compensated by the actual accumulated squared
width along the sampled path. This avoids replacing random widths by maxima. -/
theorem compensated_mgf_le {n : ℕ} (P : Process A n) (hP : P.Centered) (θ : ℝ) :
    expect P.law (fun path ↦ Real.exp (θ * P.total path - θ ^ 2 * P.energy path / 8)) ≤ 1 := by
  induction P with
  | done =>
    simp only [law, total, energy, mul_zero, zero_div, sub_self, Real.exp_zero, expect, mul_one]
    exact le_of_eq (sum_mass _)
  | step p f lo hi next ih =>
    rcases hP with ⟨hmean, hbound, hnext⟩
    rw [expect_law_step]
    have he (x : A) (path : Fin _ → A) :
        Real.exp (θ * (Process.step p f lo hi next).total (Fin.cons x path) -
          θ ^ 2 * (Process.step p f lo hi next).energy (Fin.cons x path) / 8) =
        Real.exp (θ * f x - θ ^ 2 * (hi - lo) ^ 2 / 8) *
          Real.exp (θ * (next x).total path - θ ^ 2 * (next x).energy path / 8) := by
      simp only [total, energy, Fin.cons_zero, Fin.tail_cons]
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [he]
    have hinner (x : A) : expect (next x).law (fun path ↦
        Real.exp (θ * f x - θ ^ 2 * (hi - lo) ^ 2 / 8) *
          Real.exp (θ * (next x).total path - θ ^ 2 * (next x).energy path / 8)) ≤
        Real.exp (θ * f x - θ ^ 2 * (hi - lo) ^ 2 / 8) := by
      unfold expect
      simp_rw [← mul_assoc, mul_comm (mass _ _) (Real.exp (θ * f x - θ ^ 2 * (hi - lo) ^ 2 / 8)),
        mul_assoc]
      rw [← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left (ih x (hnext x)) (Real.exp_pos _).le).trans_eq (mul_one _)
    calc
      _ ≤ expect p (fun x ↦ Real.exp (θ * f x - θ ^ 2 * (hi - lo) ^ 2 / 8)) :=
        Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hinner x) (mass_nonneg p x)
      _ = Real.exp (-(θ ^ 2 * (hi - lo) ^ 2 / 8)) *
          expect p (fun x ↦ Real.exp (θ * f x)) := by
        simp only [expect, sub_eq_add_neg, Real.exp_add, ← mul_assoc]
        rw [← Finset.sum_mul]
        ring
      _ ≤ Real.exp (-(θ ^ 2 * (hi - lo) ^ 2 / 8)) *
          Real.exp (θ ^ 2 * (hi - lo) ^ 2 / 8) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        let : MeasurableSpace A := ⊤
        let : DiscreteMeasurableSpace A := ⟨fun _ ↦ trivial⟩
        exact finite_hoeffding p f lo hi θ hbound hmean
      _ = 1 := by rw [← Real.exp_add]; simp

noncomputable def tailMass {n : ℕ} (P : Process A n) (t : ℝ) : ℝ :=
  ∑ path ∈ Finset.univ.filter (fun path ↦ t ≤ P.total path), mass P.law path

theorem tail_le_exponential {n : ℕ} (P : Process A n) (hP : P.Centered)
    (c t θ : ℝ) (hθ : 0 ≤ θ) (henergy : ∀ path, P.energy path ≤ c) :
    P.tailMass t ≤ Real.exp (-θ * t + θ ^ 2 * c / 8) := by
  classical
  have hpoint (path : Fin n → A) :
      (if t ≤ P.total path then mass P.law path * Real.exp (θ * t - θ ^ 2 * c / 8) else 0) ≤
        mass P.law path * Real.exp (θ * P.total path - θ ^ 2 * P.energy path / 8) := by
    split_ifs with ht
    · apply mul_le_mul_of_nonneg_left _ (mass_nonneg _ _)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left ht hθ,
        mul_le_mul_of_nonneg_left (henergy path) (sq_nonneg θ)]
    · exact mul_nonneg (mass_nonneg _ _) (Real.exp_pos _).le
  have hs := (Finset.sum_le_sum (fun path (_ : path ∈ Finset.univ) ↦ hpoint path)).trans
    (P.compensated_mgf_le hP θ)
  have he : (∑ path, if t ≤ P.total path then mass P.law path *
      Real.exp (θ * t - θ ^ 2 * c / 8) else 0) =
      P.tailMass t * Real.exp (θ * t - θ ^ 2 * c / 8) := by
    rw [tailMass, Finset.sum_filter, Finset.sum_mul]
    simp only [ite_mul, zero_mul]
  rw [he] at hs
  have hh := (le_div_iff₀ (Real.exp_pos (θ * t - θ ^ 2 * c / 8))).mpr hs
  rw [show -θ * t + θ ^ 2 * c / 8 = -(θ * t - θ ^ 2 * c / 8) by ring, Real.exp_neg]
  simpa only [one_div] using hh

/-- Finite branching-process form of BBCR Theorem A.1, for centered increments
and an arbitrary path-dependent sequence of conditional ranges. -/
theorem azuma {n : ℕ} (P : Process A n) (hP : P.Centered) (c t : ℝ)
    (hc : 0 < c) (ht : 0 ≤ t) (henergy : ∀ path, P.energy path ≤ c) :
    P.tailMass t ≤ Real.exp (-2 * t ^ 2 / c) := by
  have h := P.tail_le_exponential hP c t (4 * t / c) (by positivity) henergy
  have he : -(4 * t / c) * t + (4 * t / c) ^ 2 * c / 8 = -2 * t ^ 2 / c := by
    field_simp
    ring
  rwa [he] at h

end Process
end BBCR.FiniteAzuma
