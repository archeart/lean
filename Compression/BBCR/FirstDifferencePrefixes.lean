module

public import BBCR.BalancedSearch

/-! Equality of prefixes characterizes the first differing position. Appending
opposite sentinel bits handles the case of equal original strings. -/

@[expose] public section

open scoped Classical

namespace BBCR.FirstDifference

theorem take_eq_iff (a b : List Bool) (hlen : a.length = b.length) (hne : a ≠ b) (k : ℕ) :
    a.take k = b.take k ↔ k ≤ common a b := by
  induction a generalizing b k with
  | nil =>
    have hb : b = [] := List.length_eq_zero_iff.mp hlen.symm
    exact (hne hb.symm).elim
  | cons c a ih =>
    cases b with
    | nil => simp at hlen
    | cons d b =>
      cases k with
      | zero => simp
      | succ k =>
        by_cases hcd : c = d
        · subst d
          have hl : a.length = b.length := by simpa using hlen
          have hn : a ≠ b := fun h ↦ hne (congrArg (c :: ·) h)
          have hh := ih b hl hn k
          simp only [List.take_succ_cons,List.cons.injEq,true_and,common,ite_true]
          rw [hh]
          omega
        · simp [List.take_succ_cons,List.cons.injEq,common,hcd]

theorem common_lt_length (a b : List Bool) (hlen : a.length = b.length) (hne : a ≠ b) :
    common a b < a.length := by
  have hb := (common_le_length a b).1
  by_contra hh
  have he : common a b = a.length := by omega
  have ht := (take_eq_iff a b hlen hne a.length).mpr he.ge
  rw [List.take_length,List.take_of_length_le hlen.ge] at ht
  exact hne ht

def sentinel (C : ℕ) (s : Fin C → Bool) (b : Bool) : List Bool := List.ofFn s ++ [b]

theorem sentinel_ne (C : ℕ) (a b : Fin C → Bool) : sentinel C a false ≠ sentinel C b true := by
  intro h
  have hh := congrArg List.getLast? h
  simp only [sentinel,List.getLast?_concat] at hh
  contradiction

theorem sentinel_length (C : ℕ) (a : Fin C → Bool) (b : Bool) : (sentinel C a b).length = C + 1 := by
  simp [sentinel]

theorem sentinel_first_le (C : ℕ) (a b : Fin C → Bool) :
    common (sentinel C a false) (sentinel C b true) ≤ C := by
  have hh := common_lt_length _ _ (by simp [sentinel_length]) (sentinel_ne C a b)
  rw [sentinel_length] at hh
  omega

theorem membership_prefixes (t n : ℕ) (a b v : List Bool)
    (hlen : a.length = b.length) (hne : a ≠ b) (hv : v.length ≤ n)
    (hd : common a b < 2 ^ t) :
    v.IsPrefix (code t (common a b) ++ List.replicate n false) ↔
      valid t v ∧ a.take (lower t v) = b.take (lower t v) ∧
        a.take (upper t v) ≠ b.take (upper t v) := by
  have hn : a.take (upper t v) ≠ b.take (upper t v) ↔ common a b < upper t v :=
    (not_congr (take_eq_iff a b hlen hne (upper t v))).trans not_le
  rw [prefix_code t (common a b) n v hv hd,take_eq_iff a b hlen hne (lower t v),hn]

end BBCR.FirstDifference
