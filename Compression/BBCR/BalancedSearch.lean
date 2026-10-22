module

public import BBCR.NoisyTreeWalk

/-! Balanced interval addresses and their pendant chains. Membership of the
correct path reduces to two comparisons against interval endpoints. -/

@[expose] public section

open scoped Classical

namespace BBCR.FirstDifference

def lower : ℕ → List Bool → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | t + 1, b :: v => if b then 2 ^ t + lower t v else lower t v

def upper : ℕ → List Bool → ℕ
  | 0, _ => 1
  | t + 1, [] => 2 ^ (t + 1)
  | t + 1, b :: v => if b then 2 ^ t + upper t v else upper t v

def code : ℕ → ℕ → List Bool
  | 0, _ => []
  | t + 1, d => if d < 2 ^ t then false :: code t d else true :: code t (d - 2 ^ t)

def valid (t : ℕ) (v : List Bool) : Prop := ∀ b ∈ v.drop t, b = false

theorem interval_bounds (t : ℕ) (v : List Bool) : lower t v < upper t v ∧ upper t v ≤ 2 ^ t := by
  induction t generalizing v with
  | zero => simp [lower,upper]
  | succ t ih =>
    cases v with
    | nil => simp [lower,upper]
    | cons b v =>
      have hh := ih v
      have hp : 0 < 2 ^ t := by positivity
      cases b <;> simp only [lower,upper,Bool.false_eq_true,ite_false,ite_true,pow_succ] <;>
        constructor <;> omega

theorem code_length (t d : ℕ) : (code t d).length = t := by
  induction t generalizing d with
  | zero => rfl
  | succ t ih => simp only [code]; split_ifs <;> simp [ih]

theorem prefix_replicate (n : ℕ) (v : List Bool) (hv : v.length ≤ n) :
    v.IsPrefix (List.replicate n false) ↔ ∀ b ∈ v, b = false := by
  induction v generalizing n with
  | nil => simp
  | cons b v ih =>
    cases n with
    | zero => simp at hv
    | succ n =>
      have hh := ih n (by simp only [List.length_cons] at hv; omega)
      simp [List.replicate_succ,hh]

theorem prefix_code (t d n : ℕ) (v : List Bool) (hv : v.length ≤ n) (hd : d < 2 ^ t) :
    v.IsPrefix (code t d ++ List.replicate n false) ↔
      valid t v ∧ lower t v ≤ d ∧ d < upper t v := by
  induction t generalizing d v with
  | zero =>
    have he : d = 0 := by simpa using hd
    subst d
    simpa [code,valid,lower,upper] using prefix_replicate n v hv
  | succ t ih =>
    cases v with
    | nil => simp [valid,lower,upper,hd]
    | cons b v =>
      have hv' : v.length ≤ n := by simp only [List.length_cons] at hv; omega
      have hb := interval_bounds t v
      by_cases hc : d < 2 ^ t
      · cases b
        · simpa [code,hc,lower,upper,valid] using ih d v hv' hc
        · have hl : d < 2 ^ t + lower t v := by omega
          simp [code,hc,lower,upper,valid,not_le.mpr hl]
      · have hd' : d - 2 ^ t < 2 ^ t := by rw [pow_succ] at hd; omega
        cases b
        · have hu : ¬ d < upper t v := by omega
          simp [code,hc,lower,upper,valid,hu]
        · have hh := ih (d - 2 ^ t) v hv' hd'
          simp only [code,hc,ite_false,List.cons_append,List.cons_prefix_cons,true_and,
            lower,upper,ite_true,valid,List.drop_succ_cons]
          rw [hh]
          constructor <;> rintro ⟨h₁,h₂,h₃⟩ <;> exact ⟨h₁,by omega,by omega⟩

theorem lower_of_common (t d n : ℕ) (v : List Bool) (hd : d < 2 ^ t)
    (h : t ≤ common v (code t d ++ List.replicate n false)) : lower t v = d := by
  induction t generalizing d v with
  | zero => simp only [pow_zero] at hd; simp [lower,show d = 0 by omega]
  | succ t ih =>
    cases v with
    | nil => simp [common] at h
    | cons b v =>
      by_cases hc : d < 2 ^ t
      · cases b
        · have hh : t ≤ common v (code t d ++ List.replicate n false) := by
            simp only [code,hc,ite_true,List.cons_append,common,ite_true] at h
            omega
          simpa [lower] using ih d v hc hh
        · simp [code,hc,common] at h
      · have hd' : d - 2 ^ t < 2 ^ t := by rw [pow_succ] at hd; omega
        cases b
        · simp [code,hc,common] at h
        · have hh : t ≤ common v (code t (d - 2 ^ t) ++ List.replicate n false) := by
            simp only [code,hc,ite_false,List.cons_append,common,ite_true] at h
            omega
          have he := ih (d - 2 ^ t) v hd' hh
          simp only [lower,ite_true,he]
          omega

theorem lower_of_score (t d n : ℕ) (v : List Bool) (hd : d < 2 ^ t)
    (h : (t : ℝ) ≤ score v (code t d ++ List.replicate n false)) : lower t v = d := by
  have hh := (common_le_length v (code t d ++ List.replicate n false)).1
  have hr : (common v (code t d ++ List.replicate n false) : ℝ) ≤ v.length := by exact_mod_cast hh
  have hc : (t : ℝ) ≤ common v (code t d ++ List.replicate n false) := by unfold score at h; linarith
  exact lower_of_common t d n v hd (by exact_mod_cast hc)

end BBCR.FirstDifference
