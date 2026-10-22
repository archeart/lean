module

public import BBCR.ProtocolIteration

/-! Geometry of the backtracking walk used to locate the first disagreement.
The score is distance progressed along the correct path, less distance spent
on an incorrect branch. -/

@[expose] public section

open scoped Classical

namespace BBCR.FirstDifference

def common : List Bool → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => if a = b then 1 + common as bs else 0

def score (v target : List Bool) : ℝ := 2 * common v target - (v.length : ℝ)

theorem common_le_length (v target : List Bool) : common v target ≤ v.length ∧ common v target ≤ target.length := by
  induction v generalizing target with
  | nil => simp [common]
  | cons a v ih =>
    cases target with
    | nil => simp [common]
    | cons b target =>
      have hh := ih target
      by_cases h : a = b <;> simp only [common,h,ite_true,ite_false,List.length_cons] <;> omega

theorem common_of_prefix (v target : List Bool) (hv : v.IsPrefix target) : common v target = v.length := by
  obtain ⟨rest,rfl⟩ := hv
  induction v with
  | nil => rfl
  | cons a v ih => simp [common,ih,Nat.add_comm]

theorem common_append_bound (v target : List Bool) (b : Bool) :
    common v target ≤ common (v ++ [b]) target ∧ common (v ++ [b]) target ≤ common v target + 1 := by
  induction v generalizing target with
  | nil =>
    cases target with
    | nil => simp [common]
    | cons c target => by_cases h : b = c <;> simp [common,h]
  | cons a v ih =>
    cases target with
    | nil => simp [common]
    | cons c target =>
      have hh := ih target
      by_cases h : a = c <;> simp only [common,h,ite_true,ite_false,List.cons_append] <;> omega

theorem prefix_of_common_eq (v target : List Bool) (h : common v target = v.length) :
    v.IsPrefix target := by
  induction v generalizing target with
  | nil => exact List.nil_prefix
  | cons a v ih =>
    cases target with
    | nil => simp [common] at h
    | cons b target =>
      by_cases hab : a = b
      · subst b
        have hh : common v target = v.length := by simp only [common,ite_true,List.length_cons] at h; omega
        exact List.cons_prefix_cons.mpr ⟨rfl,ih target hh⟩
      · simp [common,hab] at h

theorem common_append_of_not_prefix (v target : List Bool) (b : Bool)
    (hv : ¬ v.IsPrefix target) : common (v ++ [b]) target = common v target := by
  induction v generalizing target with
  | nil => exact (hv List.nil_prefix).elim
  | cons a v ih =>
    cases target with
    | nil => simp [common]
    | cons c target =>
      by_cases hac : a = c
      · subst c
        have ht : ¬ v.IsPrefix target := by simpa using hv
        simp [common,ih target ht]
      · simp [common,hac]

theorem score_append_bound (v target : List Bool) (b : Bool) :
    score v target - 1 ≤ score (v ++ [b]) target ∧ score (v ++ [b]) target ≤ score v target + 1 := by
  have hh := common_append_bound v target b
  have h₁ : (common v target : ℝ) ≤ common (v ++ [b]) target := by exact_mod_cast hh.1
  have h₂ : (common (v ++ [b]) target : ℝ) ≤ common v target + 1 := by exact_mod_cast hh.2
  simp only [score,List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
  constructor <;> linarith

theorem score_prefix (v target : List Bool) (hv : v.IsPrefix target) : score v target = v.length := by
  rw [score,common_of_prefix v target hv]
  ring

theorem score_correct_child (v target : List Bool) (b : Bool) (hv : (v ++ [b]).IsPrefix target) :
    score (v ++ [b]) target = score v target + 1 := by
  have hp : v.IsPrefix target := (List.prefix_append v [b]).trans hv
  rw [score_prefix _ _ hv,score_prefix _ _ hp]
  simp

theorem score_parent_bound (v target : List Bool) :
    score v target - 1 ≤ score v.dropLast target ∧ score v.dropLast target ≤ score v target + 1 := by
  cases v using List.reverseRecOn with
  | nil => simp [score,common]
  | append_singleton v b =>
    have hh := score_append_bound v target b
    simp only [List.dropLast_concat]
    constructor <;> linarith

theorem score_wrong_parent (v target : List Bool) (hv : ¬ v.IsPrefix target) :
    score v.dropLast target = score v target + 1 := by
  cases v using List.reverseRecOn with
  | nil => exact (hv List.nil_prefix).elim
  | append_singleton v b =>
    have hc : common (v ++ [b]) target = common v target := by
      by_cases hp : v.IsPrefix target
      · have he := common_of_prefix v target hp
        have hh := common_append_bound v target b
        have hn : common (v ++ [b]) target ≠ (v ++ [b]).length :=
          fun h ↦ hv (prefix_of_common_eq _ _ h)
        simp only [List.length_append,List.length_singleton] at hn
        omega
      · exact common_append_of_not_prefix v target b hp
    simp only [List.dropLast_concat,score,hc,List.length_append,List.length_singleton,
      Nat.cast_add,Nat.cast_one]
    ring

end BBCR.FirstDifference
