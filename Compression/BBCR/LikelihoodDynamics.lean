module

public import BBCR.LikelihoodTrialCost

/-! The concrete likelihood trials as finite public-state dynamics. All kernels
below are derived from the protocol's actual finite seed tables. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier FiniteAzuma

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

abbrev State (p : Disjointness.Protocol X Y R SA SB) (r : R) := BoundedHistory.State (p.tree r).depth
abbrev AliceTape (p : Disjointness.Protocol X Y R SA SB) (r : R) :=
  IndexedRejection.Tape X (Candidate p r) (p.tree r).depth
abbrev BobTape (p : Disjointness.Protocol X Y R SA SB) (r : R) :=
  IndexedRejection.Tape Y (Candidate p r) (p.tree r).depth
abbrev Seeds (p : Disjointness.Protocol X Y R SA SB) (r : R) := Candidate p r × (AliceTape p r × BobTape p r)

noncomputable def stepProtocol (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (s : State p r) : Disjointness.Protocol X Y (Candidate p r) (AliceTape p r) (BobTape p r) :=
  LazyIndexedRejection.protocol (trialData p μ r s.1 ε (Real.exp 2) (Real.exp_pos _)) (leafIndex p r s.1)

noncomputable def trialOutcome (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (s : State p r) (xy : X × Y) (ω : Seeds p r) : Option (Alphabet p μ r s.1 xy) :=
  let d := trialData p μ r s.1 ε (Real.exp 2) (Real.exp_pos _)
  if ω.2.1 (xy.1,ω.1,IndexedRejection.index d ω.1 xy.1 xy.2) &&
      ω.2.2 (xy.2,ω.1,IndexedRejection.index d ω.1 xy.1 xy.2) then
    some (StoppedAzuma.finiteOutcome (p.tree r).depth (halt p μ r s.1 xy) s.1 ω.1) else none

theorem trialOutcome_decode (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (s : State p r) (xy : X × Y) (ω : Seeds p r) :
    (trialOutcome p μ ε r s xy ω).map Subtype.val =
      lazyTrialDecode p r s.1 (ω.1,(((stepProtocol p μ ε r s).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1) := by
  simp only [lazyTrialDecode, stepProtocol, LazyIndexedRejection.decoded_run, trialOutcome]
  split_ifs <;> simp [trial_index_prefix, StoppedAzuma.finiteOutcome]

theorem trialOutcome_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (s : State p r)
    (xy : X × Y) (hs : Reached p μ r xy s.1) :
    (stepProtocol p μ ε r s).seedLaw.map (trialOutcome p μ ε r s xy) =
      Rejection.attempt (observer p μ r s.1 xy)
        (TwoPartyRejection.acceptWeight (observer p μ r s.1 xy)
          (player .alice p μ r s.1 xy) (player .bob p μ r s.1 xy) (Real.exp 2))
        (TwoPartyRejection.accept_nonneg _ _ _ _ (Real.exp_pos _))
        (TwoPartyRejection.accept_le_one _ _ _ _ (Real.exp_pos _)) := by
  have hinj : Function.Injective (Option.map (Subtype.val : Alphabet p μ r s.1 xy → List Bool)) :=
    Option.map_injective Subtype.val_injective
  have hleft := Function.leftInverse_invFun hinj
  have hh := lazy_trial_law p μ ε hε hsmooth r s.1 xy hs (Real.exp 2) (Real.exp_pos _)
  change ((stepProtocol p μ ε r s).viewLaw xy.1 xy.2).map _ = _ at hh
  simp only [Protocol.viewLaw, PMF.map_comp, Function.comp_def] at hh
  have he : (fun ω : Seeds p r ↦ lazyTrialDecode p r s.1
      (ω.1,(((stepProtocol p μ ε r s).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1)) =
      fun ω ↦ (trialOutcome p μ ε r s xy ω).map Subtype.val :=
    funext (fun ω ↦ (trialOutcome_decode p μ ε r s xy ω).symm)
  rw [he] at hh
  have hf := congrArg (fun law ↦ law.map (Function.invFun (Option.map
    (Subtype.val : Alphabet p μ r s.1 xy → List Bool)))) hh
  have hi (o : Option (Alphabet p μ r s.1 xy)) : Function.invFun (Option.map
      (Subtype.val : Alphabet p μ r s.1 xy → List Bool)) (o.map Subtype.val) = o := hleft o
  simp only [PMF.map_comp, Function.comp_def, hi] at hf
  change _ = PMF.map id _ at hf
  rwa [PMF.map_id] at hf

noncomputable def acceptanceRate : ℝ := 1 / (Real.exp 2) ^ 2

theorem acceptanceRate_pos : 0 < acceptanceRate := by unfold acceptanceRate; positivity

theorem acceptanceRate_le_one : acceptanceRate ≤ 1 := by
  have hh : 1 ≤ Real.exp (2 : ℝ) := Real.one_le_exp (by norm_num)
  unfold acceptanceRate
  exact (div_le_one (by positivity)).mpr (by nlinarith)

theorem expect_trialOutcome (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (s : State p r)
    (xy : X × Y) (hs : Reached p μ r xy s.1) (g : Option (Alphabet p μ r s.1 xy) → ℝ) :
    expect (stepProtocol p μ ε r s).seedLaw (fun ω ↦ g (trialOutcome p μ ε r s xy ω)) =
      (1 - acceptanceRate) * g none + acceptanceRate * expect (target p μ r s.1 xy) (fun w ↦ g (some w)) := by
  rw [← expect_map, trialOutcome_law p μ ε hε hsmooth r s xy hs]
  obtain ⟨hrate, hp, he⟩ := exact_sampling p μ ε hε hsmooth r s.1 xy hs
  unfold expect
  rw [Rejection.expect_attempt _ _ _ _ hp g, he, hrate]
  rfl

noncomputable def advance (p : Disjointness.Protocol X Y R SA SB) (r : R) (s : State p r) (w : List Bool) : State p r :=
  if h : (s.1 ++ w).length ≤ (p.tree r).depth then ⟨s.1 ++ w,h⟩ else s

noncomputable def update (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (s : State p r) (z : Candidate p r) (bits : List Bool) : State p r :=
  (lazyTrialDecode p r s.1 (z,bits)).elim s (advance p r s)

theorem advance_frontier (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (s : State p r)
    (xy : X × Y) (hs : Reached p μ r xy s.1) (w : Alphabet p μ r s.1 xy) :
    (advance p r s w.1).1 = s.1 ++ w.1 ∧ Reached p μ r xy (advance p r s w.1).1 := by
  have hh := reached_endpoint p μ ε hε hsmooth r s.1 xy hs w
  have hl := reached_length p r xy _ hh.1
  simp only [advance, hl, dite_true]
  exact ⟨trivial,hh⟩

theorem update_run (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (s : State p r) (xy : X × Y) (ω : Seeds p r) :
    update p r s ω.1 (((stepProtocol p μ ε r s).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1 =
      (trialOutcome p μ ε r s xy ω).elim s (fun w ↦ advance p r s w.1) := by
  rw [update, ← trialOutcome_decode]
  cases trialOutcome p μ ε r s xy ω <;> rfl

abbrev Rows (p : Disjointness.Protocol X Y R SA SB) (r : R) :=
  ProtocolIteration.Rows (State p r) (Candidate p r) (AliceTape p r) (BobTape p r)

noncomputable def next (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) (ε : ℝ) (r : R) (xy : X × Y) :=
  ProtocolIteration.rowNext (stepProtocol p μ ε r) (fun s ↦ terminal p r s.1) (update p r) xy.1 xy.2

noncomputable def success (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (xy : X × Y) (s : State p r) (row : Rows p r) : Bool :=
  (trialOutcome p μ ε r s xy (row.1 s,row.2.1 s,row.2.2 s)).isSome

noncomputable def potential (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : State p r) : ℝ := residual p μ r xy s.1

theorem next_invariant (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : State p r) (hs : Reached p μ r xy s.1) (row : Rows p r) : Reached p μ r xy (next p μ ε r xy s row).1 := by
  simp only [next, ProtocolIteration.rowNext]
  split_ifs
  · exact hs
  · rw [update_run p μ ε r s xy (row.1 s,row.2.1 s,row.2.2 s)]
    cases ho : trialOutcome p μ ε r s xy (row.1 s,row.2.1 s,row.2.2 s) with
    | none => exact hs
    | some w => exact (advance_frontier p μ ε hε hsmooth r s xy hs w).2

theorem next_active (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (xy : X × Y) (s : State p r) (ht : terminal p r s.1 = false) (row : Rows p r) :
    next p μ ε r xy s row = (trialOutcome p μ ε r s xy (row.1 s,row.2.1 s,row.2.2 s)).elim
      s (fun w ↦ advance p r s w.1) := by
  simp only [next, ProtocolIteration.rowNext, ht, Bool.false_eq_true, ite_false]
  exact update_run p μ ε r s xy (row.1 s,row.2.1 s,row.2.2 s)

theorem expect_selected (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (s : State p r) (g : Seeds p r → ℝ) :
    expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r))
      (fun row : Rows p r ↦ g (row.1 s,row.2.1 s,row.2.2 s)) = expect (stepProtocol p μ ε r s).seedLaw g := by
  have hm := ProtocolIteration.row_select (stepProtocol p μ ε r) s
  have hh := congrArg (fun law ↦ expect law g) hm
  rw [expect_map] at hh
  exact hh

theorem expect_next (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : State p r) (hs : Reached p μ r xy s.1) (ht : terminal p r s.1 = false) (g : State p r → ℝ) :
    expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r)) (fun row ↦ g (next p μ ε r xy s row)) =
      (1 - acceptanceRate) * g s + acceptanceRate * expect (target p μ r s.1 xy) (fun w ↦ g (advance p r s w.1)) := by
  simp_rw [next_active p μ ε r xy s ht]
  rw [expect_selected p μ ε r s
    (fun ω ↦ g ((trialOutcome p μ ε r s xy ω).elim s (fun w ↦ advance p r s w.1)))]
  exact expect_trialOutcome p μ ε hε hsmooth r s xy hs (fun o ↦ g (o.elim s (fun w ↦ advance p r s w.1)))

theorem success_mean (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : State p r) (hs : Reached p μ r xy s.1) :
    expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r))
      (fun row ↦ if success p μ ε r xy s row then 1 else 0) = acceptanceRate := by
  unfold success
  rw [expect_selected p μ ε r s
    (fun ω ↦ if (trialOutcome p μ ε r s xy ω).isSome then 1 else 0)]
  have hh := expect_trialOutcome p μ ε hε hsmooth r s xy hs (fun o ↦ if o.isSome then 1 else 0)
  simpa only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ite_false, ite_true,
    mul_zero, zero_add, expect_const, mul_one] using hh

theorem progress_mean (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : State p r) (hs : Reached p μ r xy s.1) (ht : terminal p r s.1 = false) :
    expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r))
      (FiniteDynamics.progress (fun t ↦ terminal p r t.1) (next p μ ε r xy) (success p μ ε r xy) s) =
      acceptanceRate * probability (target p μ r s.1 xy)
        (fun w ↦ Prefix.Tree.speaker (p.tree r) (s.1 ++ w.1) ≠ none) := by
  let g : Option (Alphabet p μ r s.1 xy) → ℝ := fun o ↦ o.elim 0
    (fun w ↦ if terminal p r (advance p r s w.1).1 then 0 else 1)
  have he (row : Rows p r) : FiniteDynamics.progress (fun t ↦ terminal p r t.1)
      (next p μ ε r xy) (success p μ ε r xy) s row =
      g (trialOutcome p μ ε r s xy (row.1 s,row.2.1 s,row.2.2 s)) := by
    rw [FiniteDynamics.progress, next_active p μ ε r xy s ht]
    simp only [success, ht, Bool.not_false, Bool.true_and]
    cases ho : trialOutcome p μ ε r s xy (row.1 s,row.2.1 s,row.2.2 s) with
    | none => simp [g]
    | some w => cases hh : terminal p r (advance p r s w.1).1 <;> simp [g,hh]
  rw [funext he]
  rw [expect_selected p μ ε r s
    (fun ω ↦ g (trialOutcome p μ ε r s xy ω)), expect_trialOutcome p μ ε hε hsmooth r s xy hs]
  simp only [g, Option.elim_none, Option.elim_some, mul_zero, zero_add]
  congr 1
  unfold expect probability
  apply Finset.sum_congr rfl
  intro w _
  dsimp only
  rw [(advance_frontier p μ ε hε hsmooth r s xy hs w).1]
  by_cases hh : Prefix.Tree.speaker (p.tree r) (s.1 ++ w.1) = none <;> simp [terminal,hh]

theorem progress_budget (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : State p r) (hs : Reached p μ r xy s.1) :
    expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r)) (fun row ↦
      FiniteDynamics.progress (fun t ↦ terminal p r t.1) (next p μ ε r xy) (success p μ ε r xy) s row +
        4 * potential p μ r xy (next p μ ε r xy s row)) ≤ 4 * potential p μ r xy s := by
  cases ht : terminal p r s.1 with
  | true => simp [FiniteDynamics.progress, ht, next, ProtocolIteration.rowNext, expect_const]
  | false =>
    have hn := expect_next p μ ε hε hsmooth r xy s hs ht (potential p μ r xy)
    have he : (fun w : Alphabet p μ r s.1 xy ↦ potential p μ r xy (advance p r s w.1)) =
        fun w ↦ residual p μ r xy (s.1 ++ w.1) := by
      funext w
      exact congrArg (residual p μ r xy) (advance_frontier p μ ε hε hsmooth r s xy hs w).1
    rw [he] at hn
    have hp := progress_mean p μ ε hε hsmooth r xy s hs ht
    have hb := mul_le_mul_of_nonneg_left (nonterminal_mass_le p μ ε hε hsmooth r s.1 xy hs) acceptanceRate_pos.le
    rw [divergence_eq_residual_drop p μ ε hε hsmooth r s.1 xy hs] at hb
    rw [expect_add, hp]
    have hmul : expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r))
        (fun row ↦ 4 * potential p μ r xy (next p μ ε r xy s row)) =
        4 * expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r)) (fun row ↦ potential p μ r xy (next p μ ε r xy s row)) := by
      unfold expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row _
      ring
    rw [hmul, hn]
    dsimp only [potential]
    nlinarith

noncomputable def indexCost (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (xy : X × Y) (s : State p r) (row : Rows p r) : ℝ :=
  if terminal p r s.1 then 0 else
    ((((stepProtocol p μ ε r s).tree (row.1 s)).run (xy.1,row.2.1 s) (xy.2,row.2.2 s)).1.length : ℝ) - 4

noncomputable def indexCoefficient (p : Disjointness.Protocol X Y R SA SB) (r : R) : ℝ :=
  8 * Real.exp 4 * FrontierLocation.width (p.tree r).depth / acceptanceRate

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem indexCoefficient_nonneg (p : Disjointness.Protocol X Y R SA SB) (r : R) :
    0 ≤ indexCoefficient p r := by
  unfold indexCoefficient
  exact div_nonneg (by positivity) acceptanceRate_pos.le

theorem indexCost_nonneg (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (xy : X × Y) (s : State p r) (row : Rows p r) : 0 ≤ indexCost p μ ε r xy s row := by
  unfold indexCost
  split_ifs
  · rfl
  · have hh := LazyIndexedRejection.run_length (trialData p μ r s.1 ε (Real.exp 2) (Real.exp_pos _))
      (leafIndex p r s.1) (row.1 s) xy.1 xy.2 (row.2.1 s) (row.2.2 s)
    apply sub_nonneg.mpr
    change (4 : ℝ) ≤ ((((stepProtocol p μ ε r s).tree (row.1 s)).run (xy.1,row.2.1 s) (xy.2,row.2.2 s)).1.length : ℝ)
    apply Nat.cast_le.mpr
    change 4 ≤ (((LazyIndexedRejection.protocol _ _).tree _).run _ _).1.length
    rw [hh]
    omega

theorem index_budget (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y)
    (s : State p r) (hs : Reached p μ r xy s.1) :
    expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r)) (fun row ↦
      indexCost p μ ε r xy s row + indexCoefficient p r * potential p μ r xy (next p μ ε r xy s row)) ≤
      indexCoefficient p r * potential p μ r xy s := by
  cases ht : terminal p r s.1 with
  | true => simp [indexCost, ht, next, ProtocolIteration.rowNext, expect_const]
  | false =>
    have hn := expect_next p μ ε hε hsmooth r xy s hs ht (potential p μ r xy)
    have he : (fun w : Alphabet p μ r s.1 xy ↦ potential p μ r xy (advance p r s w.1)) =
        fun w ↦ residual p μ r xy (s.1 ++ w.1) := by
      funext w
      exact congrArg (residual p μ r xy) (advance_frontier p μ ε hε hsmooth r s xy hs w).1
    rw [he] at hn
    have hc := trial_expected_cost p μ ε hε hsmooth r s.1 xy hs
    change expect (stepProtocol p μ ε r s).seedLaw _ ≤ _ at hc
    have hi : expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r)) (indexCost p μ ε r xy s) =
        expect (stepProtocol p μ ε r s).seedLaw
          (fun ω ↦ ((((stepProtocol p μ ε r s).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1.length : ℝ)) - 4 := by
      unfold indexCost
      simp only [ht, Bool.false_eq_true, ite_false]
      rw [expect_selected p μ ε r s
        (fun ω ↦ ((((stepProtocol p μ ε r s).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1.length : ℝ) - 4)]
      simp only [expect, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_mass, one_mul]
    rw [expect_add]
    have hmul : expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r))
        (fun row ↦ indexCoefficient p r * potential p μ r xy (next p μ ε r xy s row)) =
        indexCoefficient p r * expect (ProtocolIteration.rowLaw (stepProtocol p μ ε r))
          (fun row ↦ potential p μ r xy (next p μ ε r xy s row)) := by
      unfold expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row _
      ring
    rw [hi, hmul, hn]
    have ha : indexCoefficient p r * acceptanceRate = 8 * Real.exp 4 * FrontierLocation.width (p.tree r).depth := by
      unfold indexCoefficient
      exact div_mul_cancel₀ _ acceptanceRate_pos.ne'
    change expect (stepProtocol p μ ε r s).seedLaw
      (fun ω ↦ ((((stepProtocol p μ ε r s).tree ω.1).run (xy.1,ω.2.1) (xy.2,ω.2.2)).1.length : ℝ)) ≤ _ at hc
    dsimp only [potential] at *
    nlinarith [show indexCoefficient p r * acceptanceRate * residual p μ r xy s.1 = (8 * Real.exp 4 * FrontierLocation.width (p.tree r).depth) * residual p μ r xy s.1 by rw [ha],
      show indexCoefficient p r * acceptanceRate * expect (target p μ r s.1 xy) (fun w ↦ residual p μ r xy (s.1 ++ w.1)) =
        (8 * Real.exp 4 * FrontierLocation.width (p.tree r).depth) * expect (target p μ r s.1 xy) (fun w ↦ residual p μ r xy (s.1 ++ w.1)) by rw [ha]]

theorem rowCost_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (r : R) (xy : X × Y) (s : State p r) (row : Rows p r) :
    ProtocolIteration.rowCost (stepProtocol p μ ε r) (fun s ↦ terminal p r s.1) xy.1 xy.2 s row ≤
      4 + indexCost p μ ε r xy s row := by
  simp only [ProtocolIteration.rowCost, indexCost]
  split_ifs <;> linarith

theorem completion_probability (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y) (n : ℕ) (hn : 0 < n) :
    let q := ProtocolIteration.rowLaw (stepProtocol p μ ε r)
    let root := BoundedHistory.root (p.tree r).depth
    probability (FiniteDynamics.process q (next p μ ε r xy)
      (FiniteDynamics.centeredSuccess (fun s ↦ terminal p r s.1) (success p μ ε r xy) acceptanceRate) n root).law
      (fun bits ↦ terminal p r (FiniteDynamics.stateAfter (next p μ ε r xy) n root bits).1 = false) ≤
      8 * residual p μ r xy [] / (acceptanceRate * n) + Real.exp (-(acceptanceRate ^ 2 * n / 8)) := by
  have hh := FiniteDynamics.completion_bound _ _ _ _ acceptanceRate acceptanceRate_pos acceptanceRate_le_one
    (potential p μ r xy) (fun s ↦ Reached p μ r xy s.1) 4 (by norm_num)
    (next_invariant p μ ε hε hsmooth r xy)
    (fun s hs ↦ residual_nonneg p μ ε hε₀ hε hsmooth r xy s.1 hs)
    (fun s hs row ↦ by simp [next,ProtocolIteration.rowNext,hs])
    (fun s hs _ ↦ success_mean p μ ε hε hsmooth r xy s hs)
    (progress_budget p μ ε hε hsmooth r xy) n hn (BoundedHistory.root (p.tree r).depth) (reached_nil p μ r xy)
  simpa only [potential, BoundedHistory.root, show (2 : ℝ) * 4 = 8 by norm_num] using hh

theorem expected_index_total (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 8) (hsmooth : Smooth p ε) (r : R) (xy : X × Y) (n : ℕ) :
    let q := ProtocolIteration.rowLaw (stepProtocol p μ ε r)
    let root := BoundedHistory.root (p.tree r).depth
    expect (FiniteDynamics.process q (next p μ ε r xy) (fun _ _ ↦ 0) n root).law
      (FiniteDynamics.rewardTotal (next p μ ε r xy) (indexCost p μ ε r xy) n root) ≤
      indexCoefficient p r * residual p μ r xy [] := by
  apply FiniteDynamics.reward_budget _ _ _ _ (potential p μ r xy) (fun s ↦ Reached p μ r xy s.1)
    (indexCoefficient p r) (indexCoefficient_nonneg p r)
    (next_invariant p μ ε hε hsmooth r xy)
    (fun s hs ↦ residual_nonneg p μ ε hε₀ hε hsmooth r xy s.1 hs)
    (index_budget p μ ε hε hsmooth r xy) n _ (reached_nil p μ r xy)

end BBCR.LikelihoodFrontier
