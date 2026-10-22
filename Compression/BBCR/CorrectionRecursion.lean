module

public import BBCR.FirstDifferenceSearch

/-! Deterministic correctness of the capped correction recursion. Equal local
predictions advance for free in this specification; disagreement consumes one
correction. Its communication-tree implementation is a separate obligation. -/

@[expose] public section

namespace BBCR.Correction

def path (f : List Bool → Bool) : ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, s => f s :: path f n (s ++ [f s])

def speakerBit (owner a b : List Bool → Bool) (s : List Bool) : Bool := if owner s then a s else b s

def count (owner a b : List Bool → Bool) : ℕ → List Bool → ℕ
  | 0, _ => 0
  | n + 1, s => (if a s = b s then 0 else 1) +
      count owner a b n (s ++ [speakerBit owner a b s])

def repair (owner a b : List Bool → Bool) : ℕ → ℕ → List Bool → List Bool × List Bool
  | 0, _, _ => ([],[])
  | n + 1, k, s => if a s = b s then
      let tail := repair owner a b n k (s ++ [a s])
      (a s :: tail.1,a s :: tail.2)
    else match k with
      | 0 => (path a (n + 1) s,path b (n + 1) s)
      | k + 1 =>
          let bit := speakerBit owner a b s
          let tail := repair owner a b n k (s ++ [bit])
          (bit :: tail.1,bit :: tail.2)

theorem count_le_length (owner a b : List Bool → Bool) (n : ℕ) (s : List Bool) :
    count owner a b n s ≤ n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hh := ih (s ++ [speakerBit owner a b s])
    simp only [count]
    split_ifs <;> omega

theorem repair_correct (owner a b : List Bool → Bool) (n k : ℕ) (s : List Bool)
    (h : count owner a b n s ≤ k) :
    repair owner a b n k s = (path (speakerBit owner a b) n s,path (speakerBit owner a b) n s) := by
  induction n generalizing k s with
  | zero => rfl
  | succ n ih =>
    by_cases he : a s = b s
    · have hb : speakerBit owner a b s = a s := by unfold speakerBit; split_ifs <;> simp [he]
      have ht : count owner a b n (s ++ [a s]) ≤ k := by simpa [count,he,hb] using h
      simp only [repair,ite_eq_left he]
      rw [ih k _ ht]
      simp only [path,hb]
    · have ht : 1 + count owner a b n (s ++ [speakerBit owner a b s]) ≤ k := by simpa [count,he] using h
      cases k with
      | zero => omega
      | succ k =>
        have hh : count owner a b n (s ++ [speakerBit owner a b s]) ≤ k := by omega
        simp only [repair,he,ite_false,ih k _ hh,path]

theorem zero_mistakes_local_paths (owner a b : List Bool → Bool) (n : ℕ) (s : List Bool)
    (h : count owner a b n s = 0) :
    path a n s = path (speakerBit owner a b) n s ∧
      path b n s = path (speakerBit owner a b) n s := by
  induction n generalizing s with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have he : a s = b s := by
      by_contra he
      simp only [count,he,ite_false] at h
      omega
    have hb : speakerBit owner a b s = a s := by unfold speakerBit; split_ifs <;> simp [he]
    have ht : count owner a b n (s ++ [a s]) = 0 := by simpa [count,he,hb] using h
    have hh := ih _ ht
    simp only [path,hb]
    constructor
    · exact congrArg (a s :: ·) hh.1
    · rw [← he]
      exact congrArg (a s :: ·) hh.2

end BBCR.Correction
