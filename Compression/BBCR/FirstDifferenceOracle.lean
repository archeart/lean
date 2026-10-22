module

public import BBCR.FirstDifferencePrefixes
public import BBCR.FingerprintProtocol

/-! Each interval-membership query is implemented by two finite fingerprints.
Its error is at most one eighth, uniformly at every search state. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.FirstDifference

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

abbrev String (L : ℕ) := BoundedHistory.State L

noncomputable local instance (L : ℕ) : DecidableEq (String L) := Classical.decEq _

def key (L : ℕ) (s : String L) (k : ℕ) : String L :=
  ⟨s.1.take k,by rw [List.length_take]; exact (min_le_right _ _).trans s.2⟩

noncomputable def membership (L t : ℕ) (a b : String L) (v : List Bool)
    (h : String L → Fin 16) : Bool :=
  if valid t v then decide (h (key L a (lower t v)) = h (key L b (lower t v))) &&
    !decide (h (key L a (upper t v)) = h (key L b (upper t v))) else false

theorem membership_correct (L t n : ℕ) (a b : String L) (v : List Bool)
    (hlen : a.1.length = b.1.length) (hne : a.1 ≠ b.1) (hv : v.length ≤ n)
    (hd : common a.1 b.1 < 2 ^ t) (h : String L → Fin 16)
    (h₁ : (h (key L a (lower t v)) = h (key L b (lower t v))) = (key L a (lower t v) = key L b (lower t v)))
    (h₂ : (h (key L a (upper t v)) = h (key L b (upper t v))) = (key L a (upper t v) = key L b (upper t v))) :
    membership L t a b v h = decide (v.IsPrefix (code t (common a.1 b.1) ++ List.replicate n false)) := by
  apply Bool.eq_iff_iff.mpr
  have he := membership_prefixes t n a.1 b.1 v hlen hne hv hd
  by_cases ht : valid t v
  · simp only [membership,ht,ite_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
    rw [he]
    simp only [ht,true_and]
    have hl : (h (key L a (lower t v)) = h (key L b (lower t v))) ↔ a.1.take (lower t v) = b.1.take (lower t v) := by
      simpa only [key,Subtype.mk.injEq] using Iff.of_eq h₁
    have hu : (h (key L a (upper t v)) = h (key L b (upper t v))) ↔ a.1.take (upper t v) = b.1.take (upper t v) := by
      simpa only [key,Subtype.mk.injEq] using Iff.of_eq h₂
    exact and_congr hl (not_congr hu)
  · simp [membership,ht,he]

theorem membership_error_le (L t n : ℕ) (a b : String L) (v : List Bool)
    (hlen : a.1.length = b.1.length) (hne : a.1 ≠ b.1) (hv : v.length ≤ n)
    (hd : common a.1 b.1 < 2 ^ t) :
    probability (FiniteHashing.law (String L)) (fun h ↦ membership L t a b v h ≠
      decide (v.IsPrefix (code t (common a.1 b.1) ++ List.replicate n false))) ≤ 1 / 8 := by
  let E₁ (h : String L → Fin 16) :=
    (h (key L a (lower t v)) = h (key L b (lower t v))) ≠ (key L a (lower t v) = key L b (lower t v))
  let E₂ (h : String L → Fin 16) :=
    (h (key L a (upper t v)) = h (key L b (upper t v))) ≠ (key L a (upper t v) = key L b (upper t v))
  have hs : probability (FiniteHashing.law (String L)) (fun h ↦ membership L t a b v h ≠
      decide (v.IsPrefix (code t (common a.1 b.1) ++ List.replicate n false))) ≤
      probability (FiniteHashing.law (String L)) E₁ + probability (FiniteHashing.law (String L)) E₂ := by
    apply le_trans _ (probability_or_le _ _ _)
    apply probability_mono
    intro h hh
    by_cases h₁ : E₁ h
    · exact Or.inl h₁
    · by_cases h₂ : E₂ h
      · exact Or.inr h₂
      · exact (hh (membership_correct L t n a b v hlen hne hv hd h (not_ne_iff.mp h₁) (not_ne_iff.mp h₂))).elim
  have h₁ := FiniteHashing.error_le (key L a (lower t v)) (key L b (lower t v))
  have h₂ := FiniteHashing.error_le (key L a (upper t v)) (key L b (upper t v))
  change probability _ E₁ ≤ _ at h₁
  change probability _ E₂ ≤ _ at h₂
  linarith

noncomputable def membershipTree (L t : ℕ) (v : List Bool) (h : String L → Fin 16)
    (k : Bool → Tree (String L) (String L)) : Tree (String L) (String L) :=
  FingerprintProtocol.tree h (fun a ↦ key L a (lower t v)) (fun b ↦ key L b (lower t v)) (fun lo ↦
    FingerprintProtocol.tree h (fun a ↦ key L a (upper t v)) (fun b ↦ key L b (upper t v)) (fun hi ↦
      k (if valid t v then lo && !hi else false)))

theorem membershipTree_output (L t : ℕ) (v : List Bool) (h : String L → Fin 16)
    (k : Bool → Tree (String L) (String L)) (a b : String L) :
    ((membershipTree L t v h k).run a b).2 = ((k (membership L t a b v h)).run a b).2 := by
  simp only [membershipTree,FingerprintProtocol.run,membership]

theorem membershipTree_depth (L t : ℕ) (v : List Bool) (h : String L → Fin 16)
    (k : Bool → Tree (String L) (String L)) (d : ℕ) (hk : ∀ b, (k b).depth ≤ d) :
    (membershipTree L t v h k).depth ≤ 10 + d := by
  exact (FingerprintProtocol.depth_le _ _ _ _ (5 + d) (fun _ ↦
    FingerprintProtocol.depth_le _ _ _ _ d (fun _ ↦ hk _))).trans_eq (by omega)

noncomputable def oracle (L t : ℕ) (a b : String L) (v : List Bool) (h : String L → Fin 16) : Bool × Bool :=
  (membership L t a b v h,membership L t a b (v ++ [false]) h)

noncomputable def oracleTree (L t : ℕ) (v : List Bool) (h : String L → Fin 16)
    (k : Bool × Bool → Tree (String L) (String L)) : Tree (String L) (String L) :=
  membershipTree L t v h (fun a ↦ membershipTree L t (v ++ [false]) h (fun b ↦ k (a,b)))

theorem oracleTree_output (L t : ℕ) (v : List Bool) (h : String L → Fin 16)
    (k : Bool × Bool → Tree (String L) (String L)) (a b : String L) :
    ((oracleTree L t v h k).run a b).2 = ((k (oracle L t a b v h)).run a b).2 := by
  simp only [oracleTree,membershipTree_output,oracle]

theorem oracleTree_depth (L t : ℕ) (v : List Bool) (h : String L → Fin 16)
    (k : Bool × Bool → Tree (String L) (String L)) (d : ℕ) (hk : ∀ ans, (k ans).depth ≤ d) :
    (oracleTree L t v h k).depth ≤ 20 + d := by
  exact (membershipTree_depth _ _ _ _ _ (10 + d) (fun _ ↦
    membershipTree_depth _ _ _ _ _ d (fun _ ↦ hk _))).trans_eq (by omega)

open FiniteAzuma FiniteDynamics NoisySearch

/-- The finite fingerprint oracle discharges both conditional-error premises
of the backtracking walk. No independent comparison-error hypothesis remains. -/
theorem hashed_walk_failure (L t n : ℕ) (a b : String L)
    (hlen : a.1.length = b.1.length) (hne : a.1 ≠ b.1)
    (hd : common a.1 b.1 < 2 ^ t) (hn : 0 < n) (ht : (t : ℝ) ≤ n / 4) :
    let target := code t (common a.1 b.1) ++ List.replicate n false
    let q := FiniteHashing.law (String L)
    let next := fun v h ↦ walk (oracle L t a b v h) v
    probability (process q next (centered q next (fun v ↦ score v target)) n []).law
      (fun bits ↦ score (stateAfter next n [] bits) target < t) ≤ Real.exp (-(n : ℝ) / 128) := by
  dsimp only
  apply walk_failure (FiniteHashing.law (String L)) (oracle L t a b)
    (code t (common a.1 b.1) ++ List.replicate n false) n hn (by simp [code_length]) ?_ ?_ t ht
  · intro v hv
    exact membership_error_le L t n a b v hlen hne hv.le hd
  · intro v hv
    exact membership_error_le L t n a b (v ++ [false]) hlen hne (by simp; omega) hd

theorem hashed_walk_index_error (L t n : ℕ) (a b : String L)
    (hlen : a.1.length = b.1.length) (hne : a.1 ≠ b.1)
    (hd : common a.1 b.1 < 2 ^ t) (hn : 0 < n) (ht : (t : ℝ) ≤ n / 4) :
    let target := code t (common a.1 b.1) ++ List.replicate n false
    let q := FiniteHashing.law (String L)
    let next := fun v h ↦ walk (oracle L t a b v h) v
    probability (process q next (centered q next (fun v ↦ score v target)) n []).law
      (fun bits ↦ lower t (stateAfter next n [] bits) ≠ common a.1 b.1) ≤
      Real.exp (-(n : ℝ) / 128) := by
  apply le_trans _ (hashed_walk_failure L t n a b hlen hne hd hn ht)
  apply probability_mono
  intro bits hbits
  by_contra hh
  exact hbits (lower_of_score t (common a.1 b.1) n _ hd (le_of_not_gt hh))

end BBCR.FirstDifference
