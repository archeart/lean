module

public import BBCR.FiniteCondition
public import BBCR.FiniteCoupling

/-! Finite first-hit frontiers and their normalized sampling laws. All laws
share the same stopping rule, which may depend on both inputs. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.StoppingFrontier

def paths : ℕ → (List Bool → Bool) → List Bool → Finset (List Bool)
  | 0, _, _ => {[]}
  | n + 1, halt, s => if halt s then {[]} else
      (paths n halt (s ++ [false])).image (false :: ·) ∪
        (paths n halt (s ++ [true])).image (true :: ·)

def hit : ℕ → (List Bool → Bool) → List Bool → List Bool → List Bool
  | 0, _, _, _ => []
  | n + 1, halt, s, bits => if halt s then [] else
      match bits with
      | [] => []
      | b :: rest => b :: hit n halt (s ++ [b]) rest

noncomputable def law : ℕ → (List Bool → Bool) →
    (List Bool → PMF Bool) → List Bool → PMF (List Bool)
  | 0, _, _, _ => PMF.pure []
  | n + 1, halt, K, s => if halt s then PMF.pure [] else
      (K s).bind fun b ↦ (law n halt K (s ++ [b])).map (b :: ·)

theorem branch_nil (q : PMF Bool) (K : Bool → PMF (List Bool)) :
    (q.bind fun b ↦ (K b).map (b :: ·)) [] = 0 := by
  simp [PMF.bind_apply, tsum_fintype, PMF.map_apply]

theorem branch_cons (q : PMF Bool) (K : Bool → PMF (List Bool)) (b : Bool) (w : List Bool) :
    (q.bind fun c ↦ (K c).map (c :: ·)) (b :: w) = q b * K b w := by
  cases b <;> simp [PMF.bind_apply, tsum_fintype, PMF.map_apply]

theorem mass_law_nil (n : ℕ) (halt : List Bool → Bool) (K : List Bool → PMF Bool) (s : List Bool) :
    mass (law (n + 1) halt K s) [] = if halt s then 1 else 0 := by
  cases hs : halt s with
  | true => simp [law, hs, mass]
  | false =>
    rw [law, hs]
    simp only [Bool.false_eq_true, ite_false]
    change (((K s).bind fun b ↦ (law n halt K (s ++ [b])).map (b :: ·)) []).toReal = 0
    rw [branch_nil]
    rfl

theorem mass_law_cons (n : ℕ) (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (s : List Bool) (b : Bool) (w : List Bool) :
    mass (law (n + 1) halt K s) (b :: w) =
      if halt s then 0 else mass (K s) b * mass (law n halt K (s ++ [b])) w := by
  cases hs : halt s with
  | true => simp [law, hs, mass]
  | false =>
    rw [law, hs]
    simp only [Bool.false_eq_true, ite_false]
    change (((K s).bind fun c ↦ (law n halt K (s ++ [c])).map (c :: ·)) (b :: w)).toReal = _
    rw [branch_cons, ENNReal.toReal_mul]
    rfl

theorem mass_eq_zero_of_not_mem (n : ℕ) (halt : List Bool → Bool)
    (K : List Bool → PMF Bool) (s w : List Bool) (hw : w ∉ paths n halt s) :
    mass (law n halt K s) w = 0 := by
  induction n generalizing s w with
  | zero => cases w <;> simp_all [paths, law, mass]
  | succ n ih =>
    cases hs : halt s with
    | true => cases w <;> simp_all [paths, law, mass]
    | false =>
      cases w with
      | nil => simp [mass_law_nil, hs]
      | cons b w =>
        rw [mass_law_cons, hs]
        have hc : w ∉ paths n halt (s ++ [b]) := by
          cases b <;> simpa [paths, hs] using hw
        simp [ih _ _ hc]

/-- Every complete path meets the frontier exactly once. This equivalence also
shows that frontier membership is determined by the communicated prefix. -/
theorem hit_eq_iff (n : ℕ) (halt : List Bool → Bool) (s w bits : List Bool)
    (hw : w ∈ paths n halt s) : hit n halt s bits = w ↔ w.IsPrefix bits := by
  induction n generalizing s w bits with
  | zero =>
    have he : w = [] := by simpa [paths] using hw
    subst w
    simp [hit]
  | succ n ih =>
    cases hs : halt s with
    | true =>
      have he : w = [] := by simpa [paths, hs] using hw
      subst w
      simp [hit, hs]
    | false =>
      cases w with
      | nil => simp [paths, hs] at hw
      | cons b w =>
        have hc : w ∈ paths n halt (s ++ [b]) := by
          cases b <;> simpa [paths, hs] using hw
        cases bits with
        | nil => simp [hit, hs]
        | cons c bits =>
          cases b <;> cases c <;> simp [hit, hs, ih _ _ _ hc]

theorem hit_mem (n : ℕ) (halt : List Bool → Bool) (s bits : List Bool)
    (hlen : bits.length ≤ n) (hend : halt (s ++ bits) = true) :
    hit n halt s bits ∈ paths n halt s := by
  induction n generalizing s bits with
  | zero =>
    have he : bits = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst bits
    simp [hit, paths]
  | succ n ih =>
    cases hs : halt s with
    | true => simp [hit, paths, hs]
    | false =>
      cases bits with
      | nil => simp [hs] at hend
      | cons b rest =>
        have hc := ih (s ++ [b]) rest (by simpa using hlen)
          (by simpa [List.append_assoc] using hend)
        cases b <;> simp [hit, paths, hs, hc]

theorem paths_length_le (n : ℕ) (halt : List Bool → Bool) (s w : List Bool)
    (hw : w ∈ paths n halt s) : w.length ≤ n := by
  induction n generalizing s w with
  | zero => simpa [paths] using hw
  | succ n ih =>
    cases hs : halt s with
    | true =>
      have he : w = [] := by simpa [paths, hs] using hw
      simp [he]
    | false =>
      cases w with
      | nil => simp
      | cons b w =>
        have hc : w ∈ paths n halt (s ++ [b]) := by
          cases b <;> simpa [paths, hs] using hw
        simpa using Nat.succ_le_succ (ih _ _ hc)

/-- The stopping test is false at every strict ancestor of a frontier atom. -/
theorem not_halt_take (n : ℕ) (halt : List Bool → Bool) (s w : List Bool)
    (hw : w ∈ paths n halt s) (j : ℕ) (hj : j < w.length) :
    halt (s ++ w.take j) = false := by
  induction n generalizing s w j with
  | zero =>
    have he : w = [] := by simpa [paths] using hw
    simp [he] at hj
  | succ n ih =>
    cases hs : halt s with
    | true =>
      have he : w = [] := by simpa [paths, hs] using hw
      simp [he] at hj
    | false =>
      cases w with
      | nil => simp at hj
      | cons b w =>
        have hc : w ∈ paths n halt (s ++ [b]) := by
          cases b <;> simpa [paths, hs] using hw
        cases j with
        | zero => simpa using hs
        | succ j =>
          have hh := ih (s ++ [b]) w hc j (by simpa using hj)
          simpa [List.append_assoc] using hh

theorem paths_antichain (n : ℕ) (halt : List Bool → Bool) (s u w : List Bool)
    (hu : u ∈ paths n halt s) (hw : w ∈ paths n halt s) (hp : u.IsPrefix w) : u = w := by
  have h₁ := (hit_eq_iff n halt s u w hu).mpr hp
  have h₂ := (hit_eq_iff n halt s w w hw).mpr (List.prefix_refl _)
  exact h₁.symm.trans h₂

theorem halt_or_length_eq (n : ℕ) (halt : List Bool → Bool) (s w : List Bool)
    (hw : w ∈ paths n halt s) : halt (s ++ w) = true ∨ w.length = n := by
  induction n generalizing s w with
  | zero =>
    have he : w = [] := by simpa [paths] using hw
    exact Or.inr (by simp [he])
  | succ n ih =>
    cases hs : halt s with
    | true =>
      have he : w = [] := by simpa [paths, hs] using hw
      exact Or.inl (by simpa [he] using hs)
    | false =>
      cases w with
      | nil => simp [paths, hs] at hw
      | cons b w =>
        have hc : w ∈ paths n halt (s ++ [b]) := by
          cases b <;> simpa [paths, hs] using hw
        rcases ih (s ++ [b]) w hc with hh | hh
        · exact Or.inl (by simpa using hh)
        · exact Or.inr (by simp [hh])

theorem unique_frontier_prefix (n : ℕ) (halt : List Bool → Bool) (s bits : List Bool)
    (hlen : bits.length ≤ n) (hend : halt (s ++ bits) = true) :
    ∃! w, w ∈ paths n halt s ∧ w.IsPrefix bits := by
  have hm := hit_mem n halt s bits hlen hend
  refine ⟨hit n halt s bits,⟨hm,(hit_eq_iff n halt s _ bits hm).mp rfl⟩,?_⟩
  intro w hw
  exact ((hit_eq_iff n halt s w bits hw.1).mpr hw.2).symm

/-- The fuel bound does not create an artificial endpoint on complete paths. -/
theorem halt_hit (n : ℕ) (halt : List Bool → Bool) (s bits : List Bool)
    (hlen : bits.length ≤ n) (hend : halt (s ++ bits) = true) :
    halt (s ++ hit n halt s bits) = true := by
  induction n generalizing s bits with
  | zero =>
    have he : bits = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst bits
    simpa [hit] using hend
  | succ n ih =>
    cases hs : halt s with
    | true => simp [hit, hs]
    | false =>
      cases bits with
      | nil => simp [hs] at hend
      | cons b rest =>
        have hh := ih (s ++ [b]) rest (by simpa using hlen)
          (by simpa [List.append_assoc] using hend)
        simpa [hit, hs, List.append_assoc] using hh

/-- Pointwise edge factorization survives any common first-hit rule. This is
the probabilistic core of (8.5), before instantiating the protocol kernels. -/
theorem law_factorization (n : ℕ) (halt : List Bool → Bool)
    (C P Q D : List Bool → PMF Bool)
    (hfactor : ∀ s b, mass (P s) b * mass (Q s) b = mass (C s) b * mass (D s) b)
    (s w : List Bool) :
    mass (law n halt P s) w * mass (law n halt Q s) w =
      mass (law n halt C s) w * mass (law n halt D s) w := by
  induction n generalizing s w with
  | zero => rfl
  | succ n ih =>
    cases w with
    | nil => simp only [mass_law_nil]
    | cons b w =>
      simp only [mass_law_cons]
      cases halt s <;> simp only [Bool.false_eq_true, ite_false, ite_true, mul_zero]
      calc
        _ = (mass (P s) b * mass (Q s) b) *
            (mass (law n halt P (s ++ [b])) w * mass (law n halt Q (s ++ [b])) w) := by ring
        _ = _ := by rw [hfactor, ih]; ring

/-- A potential satisfying the actual unnormalized transition identity gives
every frontier mass. This statement includes null histories. -/
theorem weighted_mass_law (n : ℕ) (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (W : List Bool → ℝ)
    (hstep : ∀ s, halt s = false → ∀ b, W s * mass (K s) b = W (s ++ [b]))
    (s w : List Bool) :
    W s * mass (law n halt K s) w = if w ∈ paths n halt s then W (s ++ w) else 0 := by
  induction n generalizing s w with
  | zero => cases w <;> simp [law, paths, mass]
  | succ n ih =>
    cases hs : halt s with
    | true => cases w <;> simp [law, paths, hs, mass]
    | false =>
      cases w with
      | nil => simp [mass_law_nil, paths, hs]
      | cons b w =>
        rw [mass_law_cons, hs]
        simp only [Bool.false_eq_true, ite_false]
        rw [← mul_assoc, hstep s hs b, ih]
        cases b <;> simp [paths, hs, List.append_assoc]

/-- Positivity propagates only along positive histories. Kernels on impossible
histories need no artificial full-support assumption. -/
theorem mass_law_pos (n : ℕ) (halt : List Bool → Bool) (K : List Bool → PMF Bool)
    (W : List Bool → ℝ)
    (hstep : ∀ s, halt s = false → ∀ b, W s * mass (K s) b = W (s ++ [b]))
    (hpositive : ∀ s, halt s = false → 0 < W s → ∀ b, 0 < mass (K s) b)
    (s w : List Bool) (hs : 0 < W s) (hw : w ∈ paths n halt s) :
    0 < mass (law n halt K s) w := by
  induction n generalizing s w with
  | zero =>
    have he : w = [] := by simpa [paths] using hw
    subst w
    simp [law, mass]
  | succ n ih =>
    cases hh : halt s with
    | true =>
      have he : w = [] := by simpa [paths, hh] using hw
      subst w
      simp [law, hh, mass]
    | false =>
      cases w with
      | nil => simp [paths, hh] at hw
      | cons b w =>
        have hc : w ∈ paths n halt (s ++ [b]) := by
          cases b <;> simpa [paths, hh] using hw
        have hb := hpositive s hh hs b
        have hs' : 0 < W (s ++ [b]) := by rw [← hstep s hh b]; exact mul_pos hs hb
        simpa only [mass_law_cons, hh, Bool.false_eq_true, ite_false] using mul_pos hb (ih _ _ hs' hc)

theorem apply_eq_zero_of_not_mem (n : ℕ) (halt : List Bool → Bool)
    (K : List Bool → PMF Bool) (s w : List Bool) (hw : w ∉ paths n halt s) :
    law n halt K s w = 0 := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) ENNReal.zero_ne_top).mp
  exact mass_eq_zero_of_not_mem n halt K s w hw

/-- The same normalized law on its common finite frontier alphabet, with no
renormalization or deletion of zero-probability frontier atoms. -/
noncomputable def finiteLaw (n : ℕ) (halt : List Bool → Bool)
    (K : List Bool → PMF Bool) (s : List Bool) : PMF ↥(paths n halt s) :=
  PMF.ofFintype (fun w ↦ law n halt K s w.1) (by
    have he : (∑' w : ↥(paths n halt s), law n halt K s w.1) = ∑' w, law n halt K s w :=
      tsum_subtype_eq_of_support_subset (by
        intro w hw
        by_contra hn
        exact hw (apply_eq_zero_of_not_mem n halt K s w hn))
    simpa only [tsum_fintype] using he.trans (law n halt K s).tsum_coe)

theorem mass_finiteLaw (n : ℕ) (halt : List Bool → Bool)
    (K : List Bool → PMF Bool) (s : List Bool) (w : ↥(paths n halt s)) :
    mass (finiteLaw n halt K s) w = mass (law n halt K s) w.1 := rfl

theorem finiteLaw_map_val (n : ℕ) (halt : List Bool → Bool)
    (K : List Bool → PMF Bool) (s : List Bool) :
    (finiteLaw n halt K s).map Subtype.val = law n halt K s := by
  apply PMF.ext
  intro w
  rw [PMF.map_apply]
  by_cases hw : w ∈ paths n halt s
  · rw [tsum_fintype, Finset.sum_eq_single ⟨w,hw⟩]
    · simp [finiteLaw]
    · intro z _ hz
      have hn : w ≠ z.1 := by
        intro he
        exact hz (Subtype.ext he.symm)
      simp only [hn, ite_false]
    · simp
  · rw [apply_eq_zero_of_not_mem n halt K s w hw]
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro z _
    split_ifs with hz
    · exact False.elim (hw (hz.symm ▸ z.2))
    · rfl

end BBCR.StoppingFrontier
