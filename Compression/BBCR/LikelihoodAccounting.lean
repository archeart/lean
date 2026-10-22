module

public import BBCR.LikelihoodFrontier
public import BBCR.KernelPotential

/-! The expected information spent at a likelihood frontier is exactly the
decrease in a residual information potential. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.StoppedAzuma

theorem pathSum_add (a b : List Bool → ℝ) (s w : List Bool) :
    pathSum (fun t ↦ a t + b t) s w = pathSum a s w + pathSum b s w := by
  induction w generalizing s with
  | nil => simp [pathSum]
  | cons bit w ih => simp only [pathSum, ih]; ring

end BBCR.StoppedAzuma

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier FiniteAzuma

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def terminal (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool) : Bool :=
  decide (Prefix.Tree.speaker (p.tree r) s = none)

noncomputable def residual (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : List Bool) : ℝ :=
  KernelPotential.value (p.tree r).depth (terminal p r) (targetKernel p μ r xy)
    (fun s ↦ Prefix.Prior.nodeDivergence p μ r s xy) s

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem terminal_depth (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : List Bool)
    (hs : (p.tree r).depth ≤ s.length) : terminal p r s = true := by
  simp [terminal, speaker_none_of_depth_le _ _ hs]

theorem terminal_implies_halt (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (s : List Bool) (hs : terminal p r s = true) :
    halt p μ r v xy s = true := by
  simp only [terminal, decide_eq_true_eq] at hs
  simp [halt, hs]

theorem residual_bellman (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : List Bool) (hs : terminal p r s = false) :
    residual p μ r xy s = Prefix.Prior.nodeDivergence p μ r s xy +
      expect (targetKernel p μ r xy s) (fun b ↦ residual p μ r xy (s ++ [b])) :=
  KernelPotential.value_bellman _ _ _ _ (terminal_depth p r) s hs

theorem residual_nonneg (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1 / 8) (hsmooth : Smooth p ε)
    (r : R) (xy : X × Y) (s : List Bool) (hr : Reached p μ r xy s) : 0 ≤ residual p μ r xy s := by
  apply KernelPotential.future_nonneg _ _ _ (Reached p μ r xy)
  · intro t hH ht b
    have hn : Prefix.Tree.speaker (p.tree r) t ≠ none := by simpa [terminal] using ht
    obtain ⟨who,howner⟩ := Option.ne_none_iff_exists'.mp hn
    exact ProtocolFrontier.reached_child p μ ε (by linarith) hsmooth r xy t hH who howner b
  · intro t hH _
    have hh := local_divergence_mem p μ ε hε₀ (by linarith) hsmooth r xy t hH
    exact add_nonneg hh.1.1 hh.2.1
  · exact hr

theorem player_expected_log (side : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) :
    expect (target p μ r v xy) (fun w ↦
      Real.log (mass (player side p μ r v xy) w / mass (observer p μ r v xy) w)) =
      expect (target p μ r v xy) (fun w ↦
        StoppedAzuma.pathSum (fun s ↦ playerDivergence side p μ r xy s) v w.1) := by
  have he (w : Alphabet p μ r v xy) := (logRatio side p μ ε hε hsmooth r v xy hr w).2.2
  simp_rw [he]
  apply StoppedAzuma.expect_incrementSum (halt p μ r v xy) (targetKernel p μ r xy)
    (fun s ↦ logIncrement (playerKernel side p μ r xy s) (Prefix.Prior.observerNext p μ r s))
    (fun s ↦ playerDivergence side p μ r xy s) (Reached p μ r xy)
    (reached_child p μ ε hε hsmooth r v xy)
  · intro s hH hstop
    obtain ⟨who,howner⟩ := active p μ r v xy s hstop
    exact (local_log_stats side p μ ε (by linarith) hsmooth r xy s hH who howner).2.1
  · exact hr

theorem divergence_eq_expected_path (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) :
    divergence (target p μ r v xy) (observer p μ r v xy) =
      expect (target p μ r v xy) (fun w ↦
        StoppedAzuma.pathSum (fun s ↦ Prefix.Prior.nodeDivergence p μ r s xy) v w.1) := by
  have hlog (w : Alphabet p μ r v xy) := TwoPartyRejection.sum_log_likelihood
    (observer p μ r v xy) (player .alice p μ r v xy) (player .bob p μ r v xy) (target p μ r v xy)
    (fun w ↦ (logRatio .alice p μ ε hε hsmooth r v xy hr w).2.1)
    (fun w ↦ (logRatio .alice p μ ε hε hsmooth r v xy hr w).1)
    (fun w ↦ (logRatio .bob p μ ε hε hsmooth r v xy hr w).1)
    (target_positive p μ ε hε hsmooth r v xy hr) (factorization p μ r v xy) w
  change expect _ _ = _
  simp_rw [← hlog]
  rw [expect_add, player_expected_log .alice p μ ε hε hsmooth r v xy hr,
    player_expected_log .bob p μ ε hε hsmooth r v xy hr, ← expect_add]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  exact (StoppedAzuma.pathSum_add _ _ v w.1).symm

theorem residual_frontier (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) :
    expect (target p μ r v xy) (fun w ↦
      StoppedAzuma.pathSum (fun s ↦ Prefix.Prior.nodeDivergence p μ r s xy) v w.1 +
        residual p μ r xy (v ++ w.1)) = residual p μ r xy v :=
  KernelPotential.stopped_expectation (terminal p r) (halt p μ r v xy) (targetKernel p μ r xy)
    (fun s ↦ Prefix.Prior.nodeDivergence p μ r s xy) (residual p μ r xy)
    (terminal_implies_halt p μ r v xy) (residual_bellman p μ r xy) _ v

theorem divergence_eq_residual_drop (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) :
    divergence (target p μ r v xy) (observer p μ r v xy) = residual p μ r xy v -
      expect (target p μ r v xy) (fun w ↦ residual p μ r xy (v ++ w.1)) := by
  have hh := residual_frontier p μ r v xy
  rw [expect_add, ← divergence_eq_expected_path p μ ε hε hsmooth r v xy hr] at hh
  linarith

theorem observer_le_target (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) (w : Alphabet p μ r v xy) :
    mass (observer p μ r v xy) w ≤ Real.exp 4 * mass (target p μ r v xy) w := by
  have hc := (logRatio .alice p μ ε hε hsmooth r v xy hr w).2.1
  have hp := (le_div_iff₀ hc).mp (likelihood_mem .alice p μ ε hε hsmooth r v xy hr w).1
  have hq := (le_div_iff₀ hc).mp (likelihood_mem .bob p μ ε hε hsmooth r v xy hr w).1
  have hm := mul_le_mul hp hq (mul_nonneg (Real.exp_pos _).le hc.le) (mass_nonneg _ _)
  have hd : mass (observer p μ r v xy) w * Real.exp (-2) ^ 2 ≤ mass (target p μ r v xy) w := by
    apply (mul_le_mul_iff_right₀ hc).mp
    calc
      _ = (Real.exp (-2) * mass (observer p μ r v xy) w) *
          (Real.exp (-2) * mass (observer p μ r v xy) w) := by ring
      _ ≤ _ := hm
      _ = _ := by rw [factorization p μ r v xy w]
  have hh := mul_le_mul_of_nonneg_left hd (Real.exp_pos (4 : ℝ)).le
  have he : Real.exp 4 * Real.exp (-2) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  nlinarith [show Real.exp 4 * (mass (observer p μ r v xy) w * Real.exp (-2) ^ 2) =
    mass (observer p μ r v xy) w by calc
      _ = mass (observer p μ r v xy) w * (Real.exp 4 * Real.exp (-2) ^ 2) := by ring
      _ = _ := by rw [he, mul_one]]

theorem observer_nonterminal_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) :
    probability (observer p μ r v xy) (fun w ↦ Prefix.Tree.speaker (p.tree r) (v ++ w.1) ≠ none) ≤
      4 * Real.exp 4 * (residual p μ r xy v -
        expect (target p μ r v xy) (fun w ↦ residual p μ r xy (v ++ w.1))) := by
  have hdom : probability (observer p μ r v xy) (fun w ↦ Prefix.Tree.speaker (p.tree r) (v ++ w.1) ≠ none) ≤
      Real.exp 4 * probability (target p μ r v xy) (fun w ↦ Prefix.Tree.speaker (p.tree r) (v ++ w.1) ≠ none) := by
    unfold probability
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    split_ifs
    · exact observer_le_target p μ ε hε hsmooth r v xy hr w
    · simp
  apply hdom.trans
  have hh := mul_le_mul_of_nonneg_left (nonterminal_mass_le p μ ε hε hsmooth r v xy hr) (Real.exp_pos (4 : ℝ)).le
  rw [divergence_eq_residual_drop p μ ε hε hsmooth r v xy hr] at hh
  nlinarith

end BBCR.LikelihoodFrontier
