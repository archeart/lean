module

public import BBCR.StoppingFrontier
public import BBCR.FiniteAzuma

/-! Realization of a stopped binary execution as a finite Azuma process.
After stopping, the extra coordinates are dummy bits with zero increment. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.StoppedAzuma

def pathSum (d : List Bool → ℝ) : List Bool → List Bool → ℝ
  | _, [] => 0
  | s, b :: w => d s + pathSum d (s ++ [b]) w

def incrementSum (z : List Bool → Bool → ℝ) : List Bool → List Bool → ℝ
  | _, [] => 0
  | s, b :: w => z s b + incrementSum z (s ++ [b]) w

def outcome : (n : ℕ) → (List Bool → Bool) → List Bool → (Fin n → Bool) → List Bool
  | 0, _, _, _ => []
  | n + 1, halt, s, bits => if halt s then [] else
      bits 0 :: outcome n halt (s ++ [bits 0]) (Fin.tail bits)

theorem outcome_eq_hit (n : ℕ) (halt : List Bool → Bool) (s : List Bool) (bits : Fin n → Bool) :
    outcome n halt s bits = StoppingFrontier.hit n halt s (List.ofFn bits) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hs : halt s with
    | true => simp [outcome, StoppingFrontier.hit, hs]
    | false =>
      simp only [outcome, StoppingFrontier.hit, List.ofFn_succ, hs, Bool.false_eq_true, ite_false, ih]
      rfl

noncomputable def process (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (z : List Bool → Bool → ℝ) (d : List Bool → ℝ) :
    (n : ℕ) → List Bool → FiniteAzuma.Process Bool n
  | 0, _ => .done
  | n + 1, s => if halt s then
      .step (PMF.pure false) (fun _ ↦ 0) 0 0 (fun _ ↦ process halt K z d n s)
    else .step (K s) (fun b ↦ z s b - d s)
      (min (z s false) (z s true) - d s) (max (z s false) (z s true) - d s)
      (fun b ↦ process halt K z d n (s ++ [b]))

theorem outcome_mem (n : ℕ) (halt : List Bool → Bool) (s : List Bool) (bits : Fin n → Bool) :
    outcome n halt s bits ∈ StoppingFrontier.paths n halt s := by
  induction n generalizing s with
  | zero => simp [outcome, StoppingFrontier.paths]
  | succ n ih =>
    cases hs : halt s with
    | true => simp [outcome, StoppingFrontier.paths, hs]
    | false =>
      have hh := ih (s ++ [bits 0]) (Fin.tail bits)
      cases hb : bits 0 <;> simpa [outcome, StoppingFrontier.paths, hs, hb] using hh

theorem invariant_take (halt : List Bool → Bool) (H : List Bool → Prop)
    (hchild : ∀ s, H s → halt s = false → ∀ b, H (s ++ [b]))
    (n : ℕ) (s w : List Bool) (hs : H s) (hw : w ∈ StoppingFrontier.paths n halt s)
    (j : ℕ) (hj : j ≤ w.length) : H (s ++ w.take j) := by
  induction n generalizing s w j with
  | zero =>
    have he : w = [] := by simpa [StoppingFrontier.paths] using hw
    subst w
    simpa using hs
  | succ n ih =>
    cases hstop : halt s with
    | true =>
      have he : w = [] := by simpa [StoppingFrontier.paths, hstop] using hw
      subst w
      simpa using hs
    | false =>
      cases w with
      | nil => simpa using hs
      | cons b w =>
        have hc : w ∈ StoppingFrontier.paths n halt (s ++ [b]) := by
          cases b <;> simpa [StoppingFrontier.paths, hstop] using hw
        cases j with
        | zero => simpa using hs
        | succ j =>
          simpa using ih (s ++ [b]) w (hchild s hs hstop b) hc j (by simpa using hj)

theorem process_law (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (z : List Bool → Bool → ℝ) (d : List Bool → ℝ) (n : ℕ) (s : List Bool) :
    (process halt K z d n s).law.map (outcome n halt s) = StoppingFrontier.law n halt K s := by
  induction n generalizing s with
  | zero => simp [process, FiniteAzuma.Process.law, outcome, StoppingFrontier.law, PMF.pure_map]
  | succ n ih =>
    cases hs : halt s with
    | true =>
      simp [process, hs, FiniteAzuma.Process.law, outcome, StoppingFrontier.law, map_constant]
    | false =>
      simp only [process, hs, Bool.false_eq_true, ite_false, FiniteAzuma.Process.law,
        PMF.map_bind, PMF.map_comp, StoppingFrontier.law]
      congr 1
      funext b
      simpa only [PMF.map_comp, Function.comp_def, outcome, hs, Bool.false_eq_true,
        ite_false, Fin.cons_zero, Fin.tail_cons] using
        congrArg (fun q ↦ q.map (b :: ·)) (ih (s ++ [b]))

theorem process_total (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (z : List Bool → Bool → ℝ) (d : List Bool → ℝ) (n : ℕ) (s : List Bool)
    (bits : Fin n → Bool) :
    (process halt K z d n s).total bits = incrementSum z s (outcome n halt s bits) -
      pathSum d s (outcome n halt s bits) := by
  induction n generalizing s with
  | zero => simp [process, FiniteAzuma.Process.total, outcome, incrementSum, pathSum]
  | succ n ih =>
    cases hs : halt s with
    | true =>
      simp only [process, hs, ite_true, FiniteAzuma.Process.total, outcome,
        incrementSum, pathSum, zero_sub, zero_add]
      rw [ih]
      -- Every later state remains stopped, so every increment vanishes.
      have hz : outcome n halt s (Fin.tail bits) = [] := by
        cases n <;> simp [outcome, hs]
      simp [hz, incrementSum, pathSum]
    | false =>
      simp only [process, hs, Bool.false_eq_true, ite_false, FiniteAzuma.Process.total,
        outcome, incrementSum, pathSum]
      rw [ih]
      ring

theorem process_centered (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (z : List Bool → Bool → ℝ) (d : List Bool → ℝ) (H : List Bool → Prop)
    (hchild : ∀ s, H s → halt s = false → ∀ b, H (s ++ [b]))
    (hmean : ∀ s, H s → halt s = false → FiniteAzuma.expect (K s) (z s) = d s)
    (n : ℕ) (s : List Bool) (hH : H s) : (process halt K z d n s).Centered := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    cases hs : halt s with
    | true =>
      simp only [process, hs, ite_true, FiniteAzuma.Process.Centered]
      refine ⟨by simp [FiniteAzuma.expect], fun _ ↦ ⟨le_rfl,le_rfl⟩, fun _ ↦ ih s hH⟩
    | false =>
      simp only [process, hs, Bool.false_eq_true, ite_false, FiniteAzuma.Process.Centered]
      refine ⟨?_, ?_, fun b ↦ ih (s ++ [b]) (hchild s hH hs b)⟩
      · simpa only [FiniteAzuma.expect, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
          sum_mass, one_mul, sub_eq_zero] using hmean s hH hs
      · intro b
        cases b <;> constructor <;> simp only [sub_le_sub_iff_right]
        · exact min_le_left _ _
        · exact le_max_left _ _
        · exact min_le_right _ _
        · exact le_max_right _ _

theorem process_energy (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (z : List Bool → Bool → ℝ) (d : List Bool → ℝ) (H : List Bool → Prop) (a : ℝ)
    (hchild : ∀ s, H s → halt s = false → ∀ b, H (s ++ [b]))
    (hwidth : ∀ s, H s → halt s = false →
      (max (z s false) (z s true) - min (z s false) (z s true)) ^ 2 ≤ a * d s)
    (n : ℕ) (s : List Bool) (hH : H s) (bits : Fin n → Bool) :
    (process halt K z d n s).energy bits ≤ a * pathSum d s (outcome n halt s bits) := by
  induction n generalizing s with
  | zero => simp [process, FiniteAzuma.Process.energy, outcome, pathSum]
  | succ n ih =>
    cases hs : halt s with
    | true =>
      simp only [process, hs, ite_true, FiniteAzuma.Process.energy,
        sub_self, zero_pow (by decide : 2 ≠ 0), zero_add, outcome, pathSum, mul_zero]
      have hh := ih s hH (Fin.tail bits)
      have hz : outcome n halt s (Fin.tail bits) = [] := by
        cases n <;> simp [outcome, hs]
      simpa only [hz, pathSum, mul_zero] using hh
    | false =>
      simp only [process, hs, Bool.false_eq_true, ite_false, FiniteAzuma.Process.energy,
        outcome, pathSum]
      have hh := ih (s ++ [bits 0]) (hchild s hH hs (bits 0)) (Fin.tail bits)
      have he : max (z s false) (z s true) - d s -
          (min (z s false) (z s true) - d s) =
          max (z s false) (z s true) - min (z s false) (z s true) := by ring
      rw [he]
      linarith [hwidth s hH hs]

theorem map_subtype_apply {A : Type*} {S : A → Prop} (q : PMF {a // S a}) (a : {a // S a}) :
    (q.map Subtype.val) a.1 = q a := by
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hb
    have hh : a.1 ≠ b.1 := fun h ↦ hb (Subtype.ext h.symm)
    simp only [hh, ite_false]

noncomputable def finiteOutcome (n : ℕ) (halt : List Bool → Bool) (s : List Bool)
    (bits : Fin n → Bool) : ↥(StoppingFrontier.paths n halt s) :=
  ⟨outcome n halt s bits, outcome_mem n halt s bits⟩

theorem process_finiteLaw (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (z : List Bool → Bool → ℝ) (d : List Bool → ℝ) (n : ℕ) (s : List Bool) :
    (process halt K z d n s).law.map (finiteOutcome n halt s) =
      StoppingFrontier.finiteLaw n halt K s := by
  apply PMF.ext
  intro w
  have hh := congrArg (fun q : PMF (List Bool) ↦ q w.1) (process_law halt K z d n s)
  have he : (process halt K z d n s).law.map (outcome n halt s) =
      ((process halt K z d n s).law.map (finiteOutcome n halt s)).map Subtype.val := by
    rw [PMF.map_comp]
    rfl
  rw [he, map_subtype_apply] at hh
  exact hh

/-- A full public candidate can be sampled before the input-dependent cutoff
is known. Applying any first-hit cutoff afterward gives its exact frontier law. -/
theorem full_process_cut (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (n : ℕ) (s : List Bool) :
    (process (fun _ ↦ false) K (fun _ _ ↦ 0) (fun _ ↦ 0) n s).law.map (outcome n halt s) =
      StoppingFrontier.law n halt K s := by
  induction n generalizing s with
  | zero => simp [process, FiniteAzuma.Process.law, outcome, StoppingFrontier.law, PMF.pure_map]
  | succ n ih =>
    cases hs : halt s with
    | true =>
      have he : outcome (n + 1) halt s = fun _ ↦ [] := by funext bits; simp [outcome, hs]
      rw [he, map_constant]
      simp [StoppingFrontier.law, hs]
    | false =>
      simp only [process, Bool.false_eq_true, ite_false, FiniteAzuma.Process.law,
        PMF.map_bind, PMF.map_comp, StoppingFrontier.law, hs]
      congr 1
      funext b
      simpa only [PMF.map_comp, Function.comp_def, outcome, hs, Bool.false_eq_true,
        ite_false, Fin.cons_zero, Fin.tail_cons] using
        congrArg (fun q ↦ q.map (b :: ·)) (ih (s ++ [b]))

theorem full_process_finite_cut (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (n : ℕ) (s : List Bool) :
    (process (fun _ ↦ false) K (fun _ _ ↦ 0) (fun _ ↦ 0) n s).law.map (finiteOutcome n halt s) =
      StoppingFrontier.finiteLaw n halt K s := by
  apply PMF.ext
  intro w
  have hh := congrArg (fun q : PMF (List Bool) ↦ q w.1) (full_process_cut halt K n s)
  have he : (process (fun _ ↦ false) K (fun _ _ ↦ 0) (fun _ ↦ 0) n s).law.map (outcome n halt s) =
      ((process (fun _ ↦ false) K (fun _ _ ↦ 0) (fun _ ↦ 0) n s).law.map
        (finiteOutcome n halt s)).map Subtype.val := by rw [PMF.map_comp]; rfl
  rw [he, map_subtype_apply] at hh
  exact hh

/-- A bound for the uncentered stopped sum. Both the drift and energy use the
actual stopped path; the ambient number of protocol bits never enters. -/
theorem increment_tail (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (z : List Bool → Bool → ℝ) (d : List Bool → ℝ) (H : List Bool → Prop)
    (hchild : ∀ s, H s → halt s = false → ∀ b, H (s ++ [b]))
    (hmean : ∀ s, H s → halt s = false → FiniteAzuma.expect (K s) (z s) = d s)
    (a : ℝ) (ha : 0 ≤ a)
    (hwidth : ∀ s, H s → halt s = false →
      (max (z s false) (z s true) - min (z s false) (z s true)) ^ 2 ≤ a * d s)
    (n : ℕ) (s : List Bool) (hH : H s) (B c t : ℝ) (hc : 0 < c) (ht : B ≤ t)
    (hB : ∀ w ∈ StoppingFrontier.paths n halt s, pathSum d s w ≤ B)
    (hBc : a * B ≤ c) :
    probability (StoppingFrontier.finiteLaw n halt K s)
      (fun w ↦ t ≤ incrementSum z s w.1) ≤ Real.exp (-2 * (t - B) ^ 2 / c) := by
  let P := process halt K z d n s
  rw [← process_finiteLaw halt K z d, probability_map]
  have hsubset : probability P.law (fun bits ↦ t ≤ incrementSum z s (outcome n halt s bits)) ≤
      P.tailMass (t - B) := by
    have he : P.tailMass (t - B) = probability P.law (fun bits ↦ t - B ≤ P.total bits) := by
      simp only [FiniteAzuma.Process.tailMass, probability, Finset.sum_filter]
    rw [he]
    apply probability_mono
    intro bits hb
    dsimp only [P]
    rw [process_total]
    linarith [hB _ (outcome_mem n halt s bits)]
  apply hsubset.trans
  apply P.azuma (process_centered halt K z d H hchild hmean n s hH) c (t - B) hc (sub_nonneg.mpr ht)
  intro bits
  exact (process_energy halt K z d H a hchild hwidth n s hH bits).trans
    ((mul_le_mul_of_nonneg_left (hB _ (outcome_mem n halt s bits)) ha).trans hBc)

end BBCR.StoppedAzuma
