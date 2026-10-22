module

public import BBCR.LikelihoodFrontier
public import BBCR.LazyIndexExchange

/-! Locality and public-leaf comparison for likelihood-excursion cutoffs. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.FrontierLocation

theorem first_mono (a b : List Bool → Bool) (h : ∀ s, a s = true → b s = true) (s w : List Bool) :
    first b s w ≤ first a s w := by
  induction w generalizing s with
  | nil => rfl
  | cons bit w ih =>
    cases ha : a s <;> cases hb : b s <;> simp only [first, ha, hb, Bool.false_eq_true, ite_false, ite_true]
    · exact Nat.add_le_add_left (ih (s ++ [bit])) 1
    · omega
    · have hh := h s ha; simp [hb] at hh
    · rfl

theorem not_halt_before_first (halt : List Bool → Bool) (s w : List Bool) (j : ℕ)
    (hj : j < first halt s w) : halt (s ++ w.take j) = false := by
  induction w generalizing s j with
  | nil => simp [first] at hj
  | cons bit w ih =>
    cases hs : halt s with
    | true => simp [first, hs] at hj
    | false =>
      cases j with
      | zero => simpa using hs
      | succ j =>
        have hh := ih (s ++ [bit]) j (by simp only [first, hs, Bool.false_eq_true, ite_false] at hj; omega)
        simpa using hh

end BBCR.FrontierLocation

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def aliceStop (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (x : X) (s : List Bool) : Bool :=
  decide (Prefix.Tree.speaker (p.tree r) s = none ∨ 1 ≤ |localSum (aliceLog p μ r x) v s|)

noncomputable def bobStop (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (y : Y) (s : List Bool) : Bool :=
  decide (Prefix.Tree.speaker (p.tree r) s = none ∨ 1 ≤ |localSum (bobLog p μ r y) v s|)

theorem halt_local (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (s : List Bool) :
    halt p μ r v xy s = (aliceStop p μ r v xy.1 s || bobStop p μ r v xy.2 s) := by
  apply Bool.eq_iff_iff.mpr
  simp only [halt, aliceStop, bobStop, Bool.or_eq_true, decide_eq_true_eq]
  tauto

theorem frontier_index_min (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (w : List Bool) (hlen : w.length ≤ (p.tree r).depth) :
    (StoppingFrontier.hit (p.tree r).depth (halt p μ r v xy) v w).length =
      min (FrontierLocation.first (aliceStop p μ r v xy.1) v w)
        (FrontierLocation.first (bobStop p μ r v xy.2) v w) := by
  rw [← FrontierLocation.first_eq_hit_length _ _ _ _ hlen]
  have he : halt p μ r v xy = fun s ↦ aliceStop p μ r v xy.1 s || bobStop p μ r v xy.2 s := by
    funext s
    exact halt_local p μ r v xy s
  rw [he, FrontierLocation.first_or]

theorem player_likelihood (side : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) (w : Alphabet p μ r v xy) :
    Real.exp (StoppedAzuma.incrementSum (fun s ↦
      logIncrement (playerKernel side p μ r xy s) (Prefix.Prior.observerNext p μ r s)) v w.1) =
      mass (player side p μ r v xy) w / mass (observer p μ r v xy) w := by
  obtain ⟨hP,hC,he⟩ := logRatio side p μ ε hε hsmooth r v xy hr w
  rw [← he, Real.exp_log (div_pos hP hC)]

end BBCR.LikelihoodFrontier
