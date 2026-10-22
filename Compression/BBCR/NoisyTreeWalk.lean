module

public import BBCR.NoisySearchDrift

/-! The backtracking search from two noisy membership comparisons per step.
The concentration proof charges comparison errors at the current state. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.NoisySearch

open FirstDifference FiniteAzuma FiniteDynamics

variable {Ω : Type} [Fintype Ω]

def walk (answers : Bool × Bool) (v : List Bool) : List Bool :=
  if answers.1 then v ++ [!answers.2] else v.dropLast

def accurate (target v : List Bool) (answers : Bool × Bool) : Prop :=
  answers.1 = decide (v.IsPrefix target) ∧ answers.2 = decide ((v ++ [false]).IsPrefix target)

omit [Fintype Ω] in
theorem walk_length (answers : Bool × Bool) (v : List Bool) : (walk answers v).length ≤ v.length + 1 := by
  unfold walk
  split_ifs <;> simp
  omega

omit [Fintype Ω] in
theorem walk_bound (answers : Bool × Bool) (v target : List Bool) :
    score v target - 1 ≤ score (walk answers v) target ∧ score (walk answers v) target ≤ score v target + 1 := by
  unfold walk
  split_ifs
  · exact score_append_bound _ _ _
  · exact score_parent_bound _ _

omit [Fintype Ω] in
theorem walk_correct (answers : Bool × Bool) (v target : List Bool)
    (hlen : v.length < target.length) (ha : accurate target v answers) :
    score (walk answers v) target = score v target + 1 := by
  rcases answers with ⟨a,b⟩
  rcases ha with ⟨rfl,rfl⟩
  by_cases hv : v.IsPrefix target
  · have hchild : (v ++ [false]).IsPrefix target ∨ (v ++ [true]).IsPrefix target := by
      obtain ⟨rest,rfl⟩ := hv
      cases rest with
      | nil => simp at hlen
      | cons bit rest =>
        cases bit
        · exact Or.inl ⟨rest,by simp⟩
        · exact Or.inr ⟨rest,by simp⟩
    by_cases hb : (v ++ [false]).IsPrefix target
    · simpa [walk,hv,hb] using score_correct_child v target false hb
    · have ht := hchild.resolve_left hb
      simpa [walk,hv,hb] using score_correct_child v target true ht
  · simpa [walk,hv] using score_wrong_parent v target hv

theorem inaccurate_le (q : PMF Ω) (oracle : List Bool → Ω → Bool × Bool) (target v : List Bool)
    (h₁ : probability q (fun ω ↦ (oracle v ω).1 ≠ decide (v.IsPrefix target)) ≤ 1 / 8)
    (h₂ : probability q (fun ω ↦ (oracle v ω).2 ≠ decide ((v ++ [false]).IsPrefix target)) ≤ 1 / 8) :
    probability q (fun ω ↦ ¬ accurate target v (oracle v ω)) ≤ 1 / 4 := by
  have hp : probability q (fun ω ↦ ¬ accurate target v (oracle v ω)) ≤
      probability q (fun ω ↦ (oracle v ω).1 ≠ decide (v.IsPrefix target)) +
      probability q (fun ω ↦ (oracle v ω).2 ≠ decide ((v ++ [false]).IsPrefix target)) := by
    apply le_trans _ (probability_or_le _ _ _)
    apply probability_mono
    intro ω hω
    simpa only [accurate,not_and_or] using hω
  linarith

theorem walk_failure (q : PMF Ω) (oracle : List Bool → Ω → Bool × Bool)
    (target : List Bool) (n : ℕ) (hn : 0 < n) (hlen : n ≤ target.length)
    (h₁ : ∀ v, v.length < n → probability q (fun ω ↦ (oracle v ω).1 ≠ decide (v.IsPrefix target)) ≤ 1 / 8)
    (h₂ : ∀ v, v.length < n → probability q (fun ω ↦ (oracle v ω).2 ≠ decide ((v ++ [false]).IsPrefix target)) ≤ 1 / 8)
    (t : ℝ) (ht : t ≤ n / 4) :
    probability (process q (fun v ω ↦ walk (oracle v ω) v)
      (centered q (fun v ω ↦ walk (oracle v ω) v) (fun v ↦ score v target)) n []).law
      (fun bits ↦ score (stateAfter (fun v ω ↦ walk (oracle v ω) v) n [] bits) target < t) ≤
      Real.exp (-(n : ℝ) / 128) := by
  apply failure_bound q _ (fun v ↦ score v target) List.length n
    (fun v ω ↦ walk_length (oracle v ω) v) ?_ ?_ n hn [] (by simp) (by simp [score,common]) t ht
  · intro v _ ω
    have hh := walk_bound (oracle v ω) v target
    change -1 ≤ score (walk (oracle v ω) v) target - score v target ∧
      score (walk (oracle v ω) v) target - score v target ≤ 1
    constructor <;> linarith [hh.1,hh.2]
  · intro v hv
    apply mean_ge_half q _ (fun v ↦ score v target) (fun v ω ↦ accurate target v (oracle v ω)) v
    · intro ω
      have hh := (walk_bound (oracle v ω) v target).1
      change -1 ≤ score (walk (oracle v ω) v) target - score v target
      linarith
    · intro ω hω
      have hh := walk_correct (oracle v ω) v target (hv.trans_le hlen) hω
      change score (walk (oracle v ω) v) target - score v target = 1
      linarith
    · exact inaccurate_le q oracle target v (h₁ v hv) (h₂ v hv)

end BBCR.NoisySearch
