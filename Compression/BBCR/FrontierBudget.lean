module

public import BBCR.ProtocolFrontier
public import BBCR.SmoothDivergence
public import BBCR.StoppedAzuma

/-! Divergence and positivity budgets on every branch of a smooth stopped
execution, including the final threshold-crossing step. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.ProtocolFrontier

theorem speaker_none_of_depth_le {A B : Type*} (t : Disjointness.Tree A B) (s : List Bool)
    (hs : t.depth ≤ s.length) : Prefix.Tree.speaker t s = none := by
  induction t generalizing s with
  | leaf o => cases s <;> rfl
  | alice q z o hz ho =>
    cases s with
    | nil => simp [Disjointness.Tree.depth] at hs
    | cons b s =>
      cases b
      · exact hz s (by simp only [Disjointness.Tree.depth, List.length_cons] at hs; omega)
      · exact ho s (by simp only [Disjointness.Tree.depth, List.length_cons] at hs; omega)
  | bob q z o hz ho =>
    cases s with
    | nil => simp [Disjointness.Tree.depth] at hs
    | cons b s =>
      cases b
      · exact hz s (by simp only [Disjointness.Tree.depth, List.length_cons] at hs; omega)
      · exact ho s (by simp only [Disjointness.Tree.depth, List.length_cons] at hs; omega)

theorem accumulated_snoc (d : List Bool → ℝ) (start : ℕ) (s : List Bool)
    (b : Bool) (hstart : start ≤ s.length) :
    accumulated d start (s ++ [b]) = accumulated d start s + d s := by
  simp only [accumulated, List.length_append, List.length_singleton]
  rw [Finset.sum_Ico_succ_top hstart]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [List.take_append_of_le_length (le_of_lt (Finset.mem_Ico.mp hj).2)]
  · simp

theorem accumulated_append (d : List Bool → ℝ) (start : ℕ) (s w : List Bool)
    (hstart : start ≤ s.length) :
    accumulated d start (s ++ w) = accumulated d start s + StoppedAzuma.pathSum d s w := by
  induction w generalizing s with
  | nil => simp [StoppedAzuma.pathSum]
  | cons b w ih =>
    rw [show s ++ b :: w = (s ++ [b]) ++ w by simp]
    rw [ih (s ++ [b]) (by simpa using Nat.le_succ_of_le hstart), accumulated_snoc d start s b hstart]
    simp only [StoppedAzuma.pathSum]
    ring

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

theorem frontier_halts (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β : ℝ) (w : List Bool)
    (hw : w ∈ StoppingFrontier.paths (p.tree r).depth (halt p μ r v xy β) v) :
    halt p μ r v xy β (v ++ w) = true := by
  rcases StoppingFrontier.halt_or_length_eq _ _ v w hw with hh | hh
  · exact hh
  · have hn := speaker_none_of_depth_le (p.tree r) (v ++ w) (by simp [hh])
    simp [halt, hn]

/-- Both the specified input pair and the observer mixture reach this history
with positive probability. This invariant is propagated along every active bit. -/
def Reached (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : List Bool) : Prop :=
  0 < Prefix.Protocol.reach p r xy.1 xy.2 s ∧ 0 < Prefix.Prior.prefixMass p μ r s

theorem targetKernel_eq_next (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : List Bool) (who : Prefix.Speaker)
    (howner : Prefix.Tree.speaker (p.tree r) s = some who)
    (hr : 0 < Prefix.Protocol.reach p r xy.1 xy.2 s) :
    targetKernel p μ r xy s = Prefix.Protocol.next p r xy.1 xy.2 s := by
  cases who with
  | alice => simp [targetKernel, howner, Prefix.Protocol.next_eq_alice p r xy.1 xy.2 s howner hr]
  | bob => simp [targetKernel, howner, Prefix.Protocol.next_eq_bob p r xy.1 xy.2 s howner hr]

theorem reached_child (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε < 1 / 2) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : List Bool) (hr : Reached p μ r xy s) (who : Prefix.Speaker)
    (howner : Prefix.Tree.speaker (p.tree r) s = some who) (b : Bool) :
    Reached p μ r xy (s ++ [b]) := by
  constructor
  · rw [← weighted_targetKernel p μ r xy s who howner b,
      targetKernel_eq_next p μ r xy s who howner hr.1]
    exact mul_pos hr.1 (lt_of_lt_of_le (by linarith)
      (hsmooth.next_mass_mem r xy.1 xy.2 s who howner hr.1 b).1)
  · rw [← weighted_observerKernel p μ r s who howner b]
    exact mul_pos hr.2 (lt_of_lt_of_le (by linarith)
      (Prefix.Prior.observerNext_mass_mem p μ ε hsmooth r s who howner hr.2 b).1)

theorem local_divergence_mem (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1 / 4) (hsmooth : Smooth p ε)
    (r : R) (xy : X × Y) (s : List Bool) (hr : Reached p μ r xy s) :
    Prefix.Prior.aliceDivergence p μ r s xy ∈ Set.Icc 0 (8 * ε) ∧
      Prefix.Prior.bobDivergence p μ r s xy ∈ Set.Icc 0 (8 * ε) := by
  have hnext (who : Prefix.Speaker) (howner : Prefix.Tree.speaker (p.tree r) s = some who) :
      divergence (Prefix.Protocol.next p r xy.1 xy.2 s) (Prefix.Prior.observerNext p μ r s)
        ∈ Set.Icc 0 (8 * ε) := by
    constructor
    · apply divergence_nonneg
      intro b hb
      have hh := (Prefix.Prior.observerNext_mass_mem p μ ε hsmooth r s who howner hr.2 b).1
      linarith
    · exact smooth_divergence_le _ _ ε hε₀ hε₁
        (fun b ↦ (hsmooth.next_mass_mem r xy.1 xy.2 s who howner hr.1 b).2)
        (fun b ↦ (Prefix.Prior.observerNext_mass_mem p μ ε hsmooth r s who howner hr.2 b).1)
  cases howner : Prefix.Tree.speaker (p.tree r) s with
  | none => simp [Prefix.Prior.aliceDivergence, Prefix.Prior.bobDivergence, howner, hε₀]
  | some who =>
    have hh := hnext who howner
    cases who with
    | alice => simpa [Prefix.Prior.aliceDivergence, Prefix.Prior.bobDivergence, howner,
        Prefix.Protocol.next_eq_alice p r xy.1 xy.2 s howner hr.1, hε₀] using hh
    | bob => simpa [Prefix.Prior.aliceDivergence, Prefix.Prior.bobDivergence, howner,
        Prefix.Protocol.next_eq_bob p r xy.1 xy.2 s howner hr.1, hε₀] using hh

theorem pathSum_budget (d : List Bool → ℝ) (v w : List Bool) (β u : ℝ) (hβ : 0 ≤ β) (hu : 0 ≤ u)
    (hpre : ∀ j < w.length, accumulated d v.length (v ++ w.take j) < β)
    (hloc : ∀ j < w.length, d (v ++ w.take j) ≤ u) :
    StoppedAzuma.pathSum d v w ≤ β + u := by
  rcases List.eq_nil_or_concat w with hw | ⟨a,b,hw⟩
  · subst w
    simp only [StoppedAzuma.pathSum]
    linarith
  · subst w
    have hj : a.length < (a.concat b).length := by simp
    have hp := hpre a.length hj
    have hl := hloc a.length hj
    simp only [List.concat_eq_append, List.take_left] at hp hl
    have he := accumulated_append d v.length v (a ++ [b]) le_rfl
    have hz : accumulated d v.length v = 0 := by simp [accumulated]
    rw [hz, zero_add] at he
    rw [List.concat_eq_append, ← he]
    rw [← List.append_assoc, accumulated_snoc d v.length (v ++ a) b (by simp)]
    linarith

theorem stopped_divergence_budget (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε β : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1 / 4) (hβ : 0 ≤ β) (hsmooth : Smooth p ε)
    (r : R) (v : List Bool) (xy : X × Y) (hr : Reached p μ r xy v)
    (w : List Bool) (hw : w ∈ StoppingFrontier.paths (p.tree r).depth (halt p μ r v xy β) v) :
    StoppedAzuma.pathSum (fun s ↦ Prefix.Prior.aliceDivergence p μ r s xy) v w ≤ β + 8 * ε ∧
      StoppedAzuma.pathSum (fun s ↦ Prefix.Prior.bobDivergence p μ r s xy) v w ≤ β + 8 * ε := by
  have hchild : ∀ s, Reached p μ r xy s → halt p μ r v xy β s = false →
      ∀ b, Reached p μ r xy (s ++ [b]) := by
    intro s hH hhalt b
    obtain ⟨who,howner⟩ := active_of_not_halt p μ r v xy β s hhalt
    exact reached_child p μ ε (by linarith) hsmooth r xy s hH who howner b
  have hloc (j : ℕ) (hj : j < w.length) := local_divergence_mem p μ ε hε₀ hε₁ hsmooth r xy
    (v ++ w.take j) (StoppedAzuma.invariant_take (halt p μ r v xy β)
      (Reached p μ r xy) hchild _ v w hr hw j hj.le)
  exact ⟨pathSum_budget _ v w β (8 * ε) hβ (by positivity)
      (fun j hj ↦ (accumulated_lt_before_frontier p μ r v xy β w hw j hj).1)
      (fun j hj ↦ (hloc j hj).1.2),
    pathSum_budget _ v w β (8 * ε) hβ (by positivity)
      (fun j hj ↦ (accumulated_lt_before_frontier p μ r v xy β w hw j hj).2)
      (fun j hj ↦ (hloc j hj).2.2)⟩

end BBCR.ProtocolFrontier
