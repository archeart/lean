module

public import BBCR.FrontierLikelihood
public import BBCR.LikelihoodCharge

/-! First exits of a fixed interval by the two local log-likelihoods.
This alternative cutoff permits exact, constant-rate rejection sampling. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.StoppedAzuma

theorem incrementSum_append (z : List Bool → Bool → ℝ) (s a b : List Bool) :
    incrementSum z s (a ++ b) = incrementSum z s a + incrementSum z (s ++ a) b := by
  induction a generalizing s with
  | nil => simp [incrementSum]
  | cons bit a ih => simp only [List.cons_append, incrementSum, ih]; simp [List.append_assoc, add_assoc]

end BBCR.StoppedAzuma

namespace BBCR

theorem logIncrement_abs_le (p q : PMF Bool) (ε : ℝ) (hε : ε ≤ 1 / 4)
    (hp : ∀ b, mass p b ∈ Set.Icc (1 / 2 - ε) (1 / 2 + ε))
    (hq : ∀ b, mass q b ∈ Set.Icc (1 / 2 - ε) (1 / 2 + ε)) (b : Bool) :
    |logIncrement p q b| ≤ 8 * ε := by
  have hp₀ : 1 / 4 ≤ mass p b := by linarith [(hp b).1]
  have hq₀ : 1 / 4 ≤ mass q b := by linarith [(hq b).1]
  have hh := abs_log_sub_le_four _ _ hp₀ hq₀
  have hdiff : |mass p b - mass q b| ≤ 2 * ε := by
    apply abs_le.mpr
    constructor <;> linarith [(hp b).1,(hp b).2,(hq b).1,(hq b).2]
  rw [logIncrement, Real.log_div (by linarith) (by linarith)]
  linarith

namespace LikelihoodFrontier

open ProtocolFrontier

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable def aliceLog (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (x : X) (s : List Bool) : Bool → ℝ :=
  logIncrement (aliceKernel p μ r x s) (Prefix.Prior.observerNext p μ r s)

noncomputable def bobLog (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (y : Y) (s : List Bool) : Bool → ℝ :=
  logIncrement (bobKernel p μ r y s) (Prefix.Prior.observerNext p μ r s)

noncomputable def localSum (z : List Bool → Bool → ℝ) (v s : List Bool) : ℝ :=
  StoppedAzuma.incrementSum z v (s.drop v.length)

noncomputable def halt (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (s : List Bool) : Bool :=
  decide (Prefix.Tree.speaker (p.tree r) s = none ∨
    1 ≤ |localSum (aliceLog p μ r xy.1) v s| ∨ 1 ≤ |localSum (bobLog p μ r xy.2) v s|)

theorem active (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (s : List Bool) (hs : halt p μ r v xy s = false) :
    ∃ who, Prefix.Tree.speaker (p.tree r) s = some who := by
  have hn : Prefix.Tree.speaker (p.tree r) s ≠ none := by
    simp only [halt, decide_eq_false_iff_not, not_or] at hs
    exact hs.1
  exact Option.ne_none_iff_exists'.mp hn

theorem interior (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (w : List Bool)
    (hw : w ∈ StoppingFrontier.paths (p.tree r).depth (halt p μ r v xy) v)
    (j : ℕ) (hj : j < w.length) :
    |StoppedAzuma.incrementSum (aliceLog p μ r xy.1) v (w.take j)| < 1 ∧
      |StoppedAzuma.incrementSum (bobLog p μ r xy.2) v (w.take j)| < 1 := by
  have hh := StoppingFrontier.not_halt_take _ (halt p μ r v xy) v w hw j hj
  simp only [halt, decide_eq_false_iff_not, not_or, not_le, localSum, List.drop_left] at hh
  exact hh.2

theorem reached_child (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool) (xy : X × Y) :
    ∀ s, Reached p μ r xy s → halt p μ r v xy s = false → ∀ b, Reached p μ r xy (s ++ [b]) := by
  intro s hH hh b
  obtain ⟨who,howner⟩ := active p μ r v xy s hh
  exact ProtocolFrontier.reached_child p μ ε (by linarith) hsmooth r xy s hH who howner b

theorem local_log_bound (side : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : List Bool) (hH : Reached p μ r xy s) (owner : Prefix.Speaker)
    (howner : Prefix.Tree.speaker (p.tree r) s = some owner) (b : Bool) :
    |logIncrement (playerKernel side p μ r xy s) (Prefix.Prior.observerNext p μ r s) b| ≤ 1 := by
  have hq := Prefix.Prior.observerNext_mass_mem p μ ε hsmooth r s owner howner hH.2
  have hp := hsmooth.next_mass_mem r xy.1 xy.2 s owner howner hH.1
  have hP : ∀ b, mass (playerKernel side p μ r xy s) b ∈ Set.Icc (1 / 2 - ε) (1 / 2 + ε) := by
    cases side <;> cases owner <;>
      simp only [playerKernel, aliceKernel, bobKernel, howner, ite_true]
    · simpa only [Prefix.Protocol.next_eq_alice p r xy.1 xy.2 s howner hH.1] using hp
    · exact hq
    · exact hq
    · simpa only [Prefix.Protocol.next_eq_bob p r xy.1 xy.2 s howner hH.1] using hp
  exact (logIncrement_abs_le _ _ ε (by linarith) hP hq b).trans (by linarith)

abbrev Alphabet (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) :=
  ↥(StoppingFrontier.paths (p.tree r).depth (halt p μ r v xy) v)

noncomputable def observer (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) : PMF (Alphabet p μ r v xy) :=
  StoppingFrontier.finiteLaw (p.tree r).depth (halt p μ r v xy) (Prefix.Prior.observerNext p μ r) v

noncomputable def player (side : Prefix.Speaker) (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) : PMF (Alphabet p μ r v xy) :=
  StoppingFrontier.finiteLaw (p.tree r).depth (halt p μ r v xy) (playerKernel side p μ r xy) v

noncomputable def target (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) : PMF (Alphabet p μ r v xy) :=
  StoppingFrontier.finiteLaw (p.tree r).depth (halt p μ r v xy) (targetKernel p μ r xy) v

theorem factorization (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (w : Alphabet p μ r v xy) :
    mass (player .alice p μ r v xy) w * mass (player .bob p μ r v xy) w =
      mass (observer p μ r v xy) w * mass (target p μ r v xy) w :=
  StoppingFrontier.law_factorization _ _ _ _ _ _ (kernel_factorization p μ r xy) v w.1

theorem stopped_log_bound (side : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) (w : Alphabet p μ r v xy) :
    |StoppedAzuma.incrementSum (fun s ↦
      logIncrement (playerKernel side p μ r xy s) (Prefix.Prior.observerNext p μ r s)) v w.1| ≤ 2 := by
  let z := fun s ↦ logIncrement (playerKernel side p μ r xy s) (Prefix.Prior.observerNext p μ r s)
  have hpre (j : ℕ) (hj : j < w.1.length) : |StoppedAzuma.incrementSum z v (w.1.take j)| < 1 := by
    have hh := interior p μ r v xy w.1 w.2 j hj
    cases side
    · exact hh.1
    · exact hh.2
  rcases List.eq_nil_or_concat w.1 with hw | ⟨a,b,hw⟩
  · simp [hw, StoppedAzuma.incrementSum]
  · have hj : a.length < w.1.length := by rw [hw]; simp
    have hp := hpre a.length hj
    simp only [hw, List.concat_eq_append, List.take_left] at hp
    have hH := StoppedAzuma.invariant_take (halt p μ r v xy) (Reached p μ r xy)
      (reached_child p μ ε hε hsmooth r v xy) _ v w.1 hr w.2 a.length hj.le
    have hstop := StoppingFrontier.not_halt_take _ (halt p μ r v xy) v w.1 w.2 a.length hj
    simp only [hw, List.concat_eq_append, List.take_left] at hH hstop
    obtain ⟨owner,howner⟩ := active p μ r v xy (v ++ a) hstop
    have hl := local_log_bound side p μ ε hε hsmooth r xy (v ++ a) hH owner howner b
    rw [hw, List.concat_eq_append, StoppedAzuma.incrementSum_append]
    simp only [StoppedAzuma.incrementSum, add_zero]
    have hh := abs_add_le (StoppedAzuma.incrementSum z v a) (z (v ++ a) b)
    exact hh.trans (by linarith)

theorem logRatio (side : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) (w : Alphabet p μ r v xy) :
    0 < mass (player side p μ r v xy) w ∧ 0 < mass (observer p μ r v xy) w ∧
      Real.log (mass (player side p μ r v xy) w / mass (observer p μ r v xy) w) =
        StoppedAzuma.incrementSum (fun s ↦
          logIncrement (playerKernel side p μ r xy s) (Prefix.Prior.observerNext p μ r s)) v w.1 := by
  apply StoppedAzuma.law_logRatio (halt p μ r v xy)
    (playerKernel side p μ r xy) (Prefix.Prior.observerNext p μ r)
    (Reached p μ r xy) (reached_child p μ ε hε hsmooth r v xy)
  · intro s hH hstop
    obtain ⟨owner,howner⟩ := active p μ r v xy s hstop
    exact (local_log_stats side p μ ε (by linarith) hsmooth r xy s hH owner howner).1
  · exact hr
  · exact w.2

theorem likelihood_mem (side : Prefix.Speaker)
    (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) (w : Alphabet p μ r v xy) :
    mass (player side p μ r v xy) w / mass (observer p μ r v xy) w ∈
      Set.Icc (Real.exp (-2)) (Real.exp 2) := by
  obtain ⟨hP,hC,he⟩ := logRatio side p μ ε hε hsmooth r v xy hr w
  have hb := stopped_log_bound side p μ ε hε hsmooth r v xy hr w
  rw [← he, abs_le] at hb
  constructor
  · exact (Real.le_log_iff_exp_le (div_pos hP hC)).mp hb.1
  · exact (Real.log_le_iff_le_exp (div_pos hP hC)).mp hb.2

theorem halt_endpoint (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (w : Alphabet p μ r v xy) :
    halt p μ r v xy (v ++ w.1) = true := by
  rcases StoppingFrontier.halt_or_length_eq _ (halt p μ r v xy) v w.1 w.2 with hh | hh
  · exact hh
  · have hn := speaker_none_of_depth_le (p.tree r) (v ++ w.1) (by simp [hh])
    simp [halt, hn]

theorem nonterminal_excursion (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) (w : Alphabet p μ r v xy)
    (hn : Prefix.Tree.speaker (p.tree r) (v ++ w.1) ≠ none) :
    1 ≤ |Real.log (mass (player .alice p μ r v xy) w / mass (observer p μ r v xy) w)| ∨
      1 ≤ |Real.log (mass (player .bob p μ r v xy) w / mass (observer p μ r v xy) w)| := by
  have hh := halt_endpoint p μ r v xy w
  simp only [halt, decide_eq_true_eq, hn, false_or, localSum, List.drop_left] at hh
  rw [(logRatio .alice p μ ε hε hsmooth r v xy hr w).2.2,
    (logRatio .bob p μ ε hε hsmooth r v xy hr w).2.2]
  exact hh

theorem target_positive (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) (w : Alphabet p μ r v xy) :
    0 < mass (target p μ r v xy) w := by
  have hp := (logRatio .alice p μ ε hε hsmooth r v xy hr w).1
  have hq := (logRatio .bob p μ ε hε hsmooth r v xy hr w).1
  have hc := (logRatio .alice p μ ε hε hsmooth r v xy hr w).2.1
  have hh := mul_pos hp hq
  rw [factorization p μ r v xy w] at hh
  exact pos_of_mul_pos_right hh hc.le

/-- Fixed log-likelihood cutoffs give an exact accepted frontier, with the
same constant acceptance rate at every reached prefix and input pair. -/
theorem exact_sampling (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) :
    let C := observer p μ r v xy
    let P := player .alice p μ r v xy
    let Q := player .bob p μ r v xy
    let D := target p μ r v xy
    Rejection.rate C (TwoPartyRejection.acceptWeight C P Q (Real.exp 2)) = 1 / (Real.exp 2) ^ 2 ∧
      ∃ hrate : 0 < Rejection.rate C (TwoPartyRejection.acceptWeight C P Q (Real.exp 2)),
        Rejection.accepted C (TwoPartyRejection.acceptWeight C P Q (Real.exp 2))
          (TwoPartyRejection.accept_nonneg _ _ _ _ (Real.exp_pos _)) hrate = D := by
  have hC := fun w ↦ (logRatio .alice p μ ε hε hsmooth r v xy hr w).2.1
  have hP := fun w ↦ (div_le_iff₀ (hC w)).mp (likelihood_mem .alice p μ ε hε hsmooth r v xy hr w).2
  have hQ := fun w ↦ (div_le_iff₀ (hC w)).mp (likelihood_mem .bob p μ ε hε hsmooth r v xy hr w).2
  exact ⟨TwoPartyRejection.exact_rate _ _ _ _ _ (Real.exp_pos _) hC (factorization p μ r v xy) hP hQ,
    TwoPartyRejection.exact_accepted _ _ _ _ _ (Real.exp_pos _) hC (factorization p μ r v xy) hP hQ⟩

/-- The nonterminal round charge has no reciprocal smoothness parameter. -/
theorem nonterminal_mass_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (v : List Bool)
    (xy : X × Y) (hr : Reached p μ r xy v) :
    probability (target p μ r v xy) (fun w ↦ Prefix.Tree.speaker (p.tree r) (v ++ w.1) ≠ none) ≤
      4 * divergence (target p μ r v xy) (observer p μ r v xy) := by
  apply (probability_mono _ _ _ (nonterminal_excursion p μ ε hε hsmooth r v xy hr)).trans
  exact TwoPartyRejection.excursion_mass_le _ _ _ _
    (fun w ↦ (logRatio .alice p μ ε hε hsmooth r v xy hr w).2.1)
    (fun w ↦ (logRatio .alice p μ ε hε hsmooth r v xy hr w).1)
    (fun w ↦ (logRatio .bob p μ ε hε hsmooth r v xy hr w).1)
    (target_positive p μ ε hε hsmooth r v xy hr) (factorization p μ r v xy)

end LikelihoodFrontier
end BBCR
