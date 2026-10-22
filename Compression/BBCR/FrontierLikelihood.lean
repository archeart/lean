module

public import BBCR.FrontierBudget
public import BBCR.StoppedLikelihood
public import BBCR.FrontierRejection

/-! BBCR Claim 8.9 for the actual input-dependent frontier. All local means,
ranges, and accumulated variance bounds are derived from protocol smoothness. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.ProtocolFrontier

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def playerKernel (who : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : List Bool) : PMF Bool :=
  match who with
  | .alice => aliceKernel p μ r xy.1 s
  | .bob => bobKernel p μ r xy.2 s

noncomputable def playerDivergence (who : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : List Bool) : ℝ :=
  match who with
  | .alice => Prefix.Prior.aliceDivergence p μ r s xy
  | .bob => Prefix.Prior.bobDivergence p μ r s xy

theorem local_log_stats (side : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 4) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : List Bool) (hr : Reached p μ r xy s) (owner : Prefix.Speaker)
    (howner : Prefix.Tree.speaker (p.tree r) s = some owner) :
    let P := playerKernel side p μ r xy s
    let C := Prefix.Prior.observerNext p μ r s
    let d := playerDivergence side p μ r xy s
    (∀ b, 0 < mass P b ∧ 0 < mass C b) ∧
      FiniteAzuma.expect (targetKernel p μ r xy s) (logIncrement P C) = d ∧
      (max (logIncrement P C false) (logIncrement P C true) -
        min (logIncrement P C false) (logIncrement P C true)) ^ 2 ≤ 64 * d := by
  dsimp only
  let q := Prefix.Prior.observerNext p μ r s
  let pi := Prefix.Protocol.next p r xy.1 xy.2 s
  have hq (b : Bool) : 1 / 4 ≤ mass q b := by
    have hh := (Prefix.Prior.observerNext_mass_mem p μ ε hsmooth r s owner howner hr.2 b).1
    dsimp only [q]
    linarith
  have hpi (b : Bool) : 1 / 4 ≤ mass pi b := by
    have hh := (hsmooth.next_mass_mem r xy.1 xy.2 s owner howner hr.1 b).1
    dsimp only [pi]
    linarith
  have heP : playerKernel side p μ r xy s = if side = owner then pi else q := by
    cases side <;> cases owner <;>
      simp [playerKernel, aliceKernel, bobKernel, howner, pi, q,
        Prefix.Protocol.next_eq_alice p r xy.1 xy.2 s, Prefix.Protocol.next_eq_bob p r xy.1 xy.2 s, hr.1]
  have hed : playerDivergence side p μ r xy s = if side = owner then divergence pi q else 0 := by
    cases side <;> cases owner <;>
      simp [playerDivergence, Prefix.Prior.aliceDivergence, Prefix.Prior.bobDivergence,
        howner, pi, q, Prefix.Protocol.next_eq_alice p r xy.1 xy.2 s,
        Prefix.Protocol.next_eq_bob p r xy.1 xy.2 s, hr.1]
  rw [heP, hed, targetKernel_eq_next p μ r xy s owner howner hr.1]
  change (∀ b, 0 < mass (if side = owner then pi else q) b ∧ 0 < mass q b) ∧ _
  by_cases he : side = owner
  · simp only [he, ite_true]
    exact ⟨fun b ↦ ⟨by linarith [hpi b], by linarith [hq b]⟩,
      expect_logIncrement pi q, logIncrement_width_sq pi q hpi hq⟩
  · simp only [he, ite_false]
    have hz : logIncrement q q = fun _ ↦ 0 := by
      funext b
      simp [logIncrement, ne_of_gt (show 0 < mass q b by linarith [hq b])]
    change (∀ b, 0 < mass q b ∧ 0 < mass q b) ∧
      FiniteAzuma.expect pi (logIncrement q q) = 0 ∧
      (max (logIncrement q q false) (logIncrement q q true) -
        min (logIncrement q q false) (logIncrement q q true)) ^ 2 ≤ 64 * 0
    rw [hz]
    exact ⟨fun b ↦ ⟨by linarith [hq b], by linarith [hq b]⟩,
      by simp [FiniteAzuma.expect], by norm_num⟩

theorem player_logRatio_tail (side : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β : ℝ) (hβ₀ : 0 < β) (hβ₁ : β ≤ 1 / 4) (hsmooth : Smooth p β)
    (r : R) (v : List Bool) (xy : X × Y) (hr : Reached p μ r xy v)
    (t : ℝ) (ht : 9 * β ≤ t) :
    probability (targetFinite p μ r v xy β) (fun w ↦ t ≤
      Real.log (mass (StoppingFrontier.finiteLaw (p.tree r).depth (halt p μ r v xy β)
        (playerKernel side p μ r xy) v) w / mass (observerFinite p μ r v xy β) w)) ≤
      Real.exp (-2 * (t - 9 * β) ^ 2 / (576 * β)) := by
  have hchild : ∀ s, Reached p μ r xy s → halt p μ r v xy β s = false →
      ∀ b, Reached p μ r xy (s ++ [b]) := by
    intro s hH hhalt b
    obtain ⟨owner,howner⟩ := active_of_not_halt p μ r v xy β s hhalt
    exact reached_child p μ β (by linarith) hsmooth r xy s hH owner howner b
  have hstats (s : List Bool) (hH : Reached p μ r xy s) (hhalt : halt p μ r v xy β s = false) :=
    let owner := (active_of_not_halt p μ r v xy β s hhalt).choose
    local_log_stats side p μ β hβ₁ hsmooth r xy s hH owner
      (active_of_not_halt p μ r v xy β s hhalt).choose_spec
  apply StoppedAzuma.logRatio_tail (halt p μ r v xy β) (targetKernel p μ r xy)
    (playerKernel side p μ r xy) (Prefix.Prior.observerNext p μ r)
    (playerDivergence side p μ r xy) (Reached p μ r xy) hchild
    (fun s hH hh ↦ (hstats s hH hh).1) (fun s hH hh ↦ (hstats s hH hh).2.1)
    64 (by norm_num) (fun s hH hh ↦ (hstats s hH hh).2.2)
    (p.tree r).depth v hr (9 * β) (576 * β) t (by positivity) ht
  · intro w hw
    have hh := stopped_divergence_budget p μ β β hβ₀.le hβ₁ hβ₀.le hsmooth r v xy hr w hw
    cases side with
    | alice =>
      change StoppedAzuma.pathSum (fun s ↦ Prefix.Prior.aliceDivergence p μ r s xy) v w ≤ _
      linarith [hh.1]
    | bob =>
      change StoppedAzuma.pathSum (fun s ↦ Prefix.Prior.bobDivergence p μ r s xy) v w ≤ _
      linarith [hh.2]
  · ring_nf
    exact le_rfl

/-- The target mass lost by clipping either player's likelihood ratio is
bounded solely by smoothness, the frontier threshold, and the clipping level. -/
theorem badMass_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β : ℝ) (hβ₀ : 0 < β) (hβ₁ : β ≤ 1 / 4) (hsmooth : Smooth p β)
    (r : R) (v : List Bool) (xy : X × Y) (hr : Reached p μ r xy v)
    (t : ℝ) (ht : 0 < t) (hlog : 9 * β ≤ Real.log t) :
    TwoPartyRejection.badMass (observerFinite p μ r v xy β) (aliceFinite p μ r v xy β)
      (bobFinite p μ r v xy β) (targetFinite p μ r v xy β) t ≤
        2 * Real.exp (-2 * (Real.log t - 9 * β) ^ 2 / (576 * β)) := by
  have ha := player_logRatio_tail .alice p μ β hβ₀ hβ₁ hsmooth r v xy hr (Real.log t) hlog
  have hb := player_logRatio_tail .bob p μ β hβ₀ hβ₁ hsmooth r v xy hr (Real.log t) hlog
  change probability (targetFinite p μ r v xy β) (fun w ↦ Real.log t ≤
    Real.log (mass (aliceFinite p μ r v xy β) w / mass (observerFinite p μ r v xy β) w)) ≤ _ at ha
  change probability (targetFinite p μ r v xy β) (fun w ↦ Real.log t ≤
    Real.log (mass (bobFinite p μ r v xy β) w / mass (observerFinite p μ r v xy β) w)) ≤ _ at hb
  have hC := observer_positive p μ r v xy β β hsmooth (by linarith) hr.2
  have hpoint (P : PMF (Alphabet p μ r v xy β)) (w : Alphabet p μ r v xy β)
      (hw : t * mass (observerFinite p μ r v xy β) w < mass P w) :
      Real.log t ≤ Real.log (mass P w / mass (observerFinite p μ r v xy β) w) :=
    Real.log_le_log ht ((lt_div_iff₀ (hC w)).mpr hw).le
  have hrewrite : TwoPartyRejection.badMass (observerFinite p μ r v xy β)
      (aliceFinite p μ r v xy β) (bobFinite p μ r v xy β) (targetFinite p μ r v xy β) t =
      probability (targetFinite p μ r v xy β) (fun w ↦
        t * mass (observerFinite p μ r v xy β) w < mass (aliceFinite p μ r v xy β) w ∨
        t * mass (observerFinite p μ r v xy β) w < mass (bobFinite p μ r v xy β) w) := by
    simp only [TwoPartyRejection.badMass, TwoPartyRejection.badSet, Finset.sum_filter, probability]
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> rfl
  rw [hrewrite]
  calc
    _ ≤ probability (targetFinite p μ r v xy β) (fun w ↦
        Real.log t ≤ Real.log (mass (aliceFinite p μ r v xy β) w / mass (observerFinite p μ r v xy β) w) ∨
        Real.log t ≤ Real.log (mass (bobFinite p μ r v xy β) w / mass (observerFinite p μ r v xy β) w)) := by
      apply probability_mono
      intro w hw
      exact hw.imp (hpoint _ w) (hpoint _ w)
    _ ≤ _ := (probability_or_le _ _ _).trans (by linarith)

/-- A constant clipping level suffices: bad mass is exponentially small in
the reciprocal smoothness parameter. This is the quantitative Claim 8.9. -/
theorem badMass_exp_one (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β : ℝ) (hβ₀ : 0 < β) (hβ₁ : β ≤ 1 / 18) (hsmooth : Smooth p β)
    (r : R) (v : List Bool) (xy : X × Y) (hr : Reached p μ r xy v) :
    TwoPartyRejection.badMass (observerFinite p μ r v xy β) (aliceFinite p μ r v xy β)
      (bobFinite p μ r v xy β) (targetFinite p μ r v xy β) (Real.exp 1) ≤
        2 * Real.exp (-(1 / (1152 * β))) := by
  have h := badMass_le p μ β hβ₀ (by linarith) hsmooth r v xy hr (Real.exp 1)
    (Real.exp_pos _) (by rw [Real.log_exp]; linarith)
  rw [Real.log_exp] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have he : -(1 / (1152 * β)) = -(1 / 2) / (576 * β) := by ring
  rw [he]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 576 * β)).mpr
  nlinarith [sq_nonneg (1 - 9 * β - 1 / 2)]

theorem player_likelihood (side : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β : ℝ) (hβ : β ≤ 1 / 4) (hsmooth : Smooth p β)
    (r : R) (v : List Bool) (xy : X × Y) (hr : Reached p μ r xy v)
    (w : Alphabet p μ r v xy β) :
    Real.exp (StoppedAzuma.incrementSum (fun s ↦
      logIncrement (playerKernel side p μ r xy s) (Prefix.Prior.observerNext p μ r s)) v w.1) =
      mass (StoppingFrontier.finiteLaw (p.tree r).depth (halt p μ r v xy β)
        (playerKernel side p μ r xy) v) w / mass (observerFinite p μ r v xy β) w := by
  have hchild : ∀ s, Reached p μ r xy s → halt p μ r v xy β s = false →
      ∀ b, Reached p μ r xy (s ++ [b]) := by
    intro s hH hh b
    obtain ⟨owner,howner⟩ := active_of_not_halt p μ r v xy β s hh
    exact reached_child p μ β (by linarith) hsmooth r xy s hH owner howner b
  have hpos : ∀ s, Reached p μ r xy s → halt p μ r v xy β s = false → ∀ b,
      0 < mass (playerKernel side p μ r xy s) b ∧ 0 < mass (Prefix.Prior.observerNext p μ r s) b := by
    intro s hH hh
    obtain ⟨owner,howner⟩ := active_of_not_halt p μ r v xy β s hh
    exact (local_log_stats side p μ β hβ hsmooth r xy s hH owner howner).1
  obtain ⟨hP,hC,he⟩ := StoppedAzuma.law_logRatio (halt p μ r v xy β)
    (playerKernel side p μ r xy) (Prefix.Prior.observerNext p μ r)
    (Reached p μ r xy) hchild hpos (p.tree r).depth v w.1 hr w.2
  rw [← he, Real.exp_log (div_pos hP hC)]
  rfl

end BBCR.ProtocolFrontier
