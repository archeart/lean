module

public import BBCR.FrontierTrial
public import BBCR.LikelihoodLocation
public import BBCR.ResidualInformation

/-! An exact likelihood-frontier trial using locally computed cutoffs. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR.LikelihoodFrontier

open ProtocolFrontier

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

abbrev Candidate (p : Disjointness.Protocol X Y R SA SB) (r : R) := Fin (p.tree r).depth → Bool

noncomputable def candidateLaw (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) : PMF (Candidate p r) :=
  (StoppedAzuma.process (fun _ ↦ false) (Prefix.Prior.observerNext p μ r)
    (fun _ _ ↦ 0) (fun _ ↦ 0) (p.tree r).depth v).law

/-- The public candidate law does not contain either actual input. Its
pushforward by the joint cutoff is exactly the observer frontier distribution. -/
theorem candidateLaw_frontier (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (_β : ℝ) :
    (candidateLaw p μ r v).map (StoppedAzuma.finiteOutcome (p.tree r).depth (halt p μ r v xy) v) =
      observer p μ r v xy :=
  StoppedAzuma.full_process_finite_cut _ _ _ _

noncomputable def trialData (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (_β t : ℝ) (ht : 0 < t) : IndexedRejection.Data X Y (Candidate p r) (p.tree r).depth where
  proposal := candidateLaw p μ r v
  aliceIndex bits x := ⟨FrontierLocation.first (aliceStop p μ r v x) v (List.ofFn bits), by
    have hh := FrontierLocation.first_le (aliceStop p μ r v x) v (List.ofFn bits)
    simpa using Nat.lt_succ_of_le hh⟩
  bobIndex bits y := ⟨FrontierLocation.first (bobStop p μ r v y) v (List.ofFn bits), by
    have hh := FrontierLocation.first_le (bobStop p μ r v y) v (List.ofFn bits)
    simpa using Nat.lt_succ_of_le hh⟩
  aliceAccept x bits i := min 1 (Real.exp (StoppedAzuma.incrementSum
    (fun s ↦ logIncrement (aliceKernel p μ r x s) (Prefix.Prior.observerNext p μ r s)) v
    ((List.ofFn bits).take i.val)) / t)
  bobAccept y bits i := min 1 (Real.exp (StoppedAzuma.incrementSum
    (fun s ↦ logIncrement (bobKernel p μ r y s) (Prefix.Prior.observerNext p μ r s)) v
    ((List.ofFn bits).take i.val)) / t)
  alice_nonneg _ _ _ := le_min (by norm_num) (div_nonneg (Real.exp_pos _).le ht.le)
  bob_nonneg _ _ _ := le_min (by norm_num) (div_nonneg (Real.exp_pos _).le ht.le)
  alice_le_one _ _ _ := min_le_left _ _
  bob_le_one _ _ _ := min_le_left _ _

theorem trial_index_prefix (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (xy : X × Y) (β t : ℝ) (ht : 0 < t) (bits : Candidate p r) :
    (List.ofFn bits).take (IndexedRejection.index (trialData p μ r v β t ht) bits xy.1 xy.2).val =
      StoppedAzuma.outcome (p.tree r).depth (halt p μ r v xy) v bits := by
  change (List.ofFn bits).take (min
    (FrontierLocation.first (aliceStop p μ r v xy.1) v (List.ofFn bits))
    (FrontierLocation.first (bobStop p μ r v xy.2) v (List.ofFn bits))) = _
  rw [← frontier_index_min p μ r v xy (List.ofFn bits) (by simp),
    ← FrontierLocation.first_eq_hit_length (halt p μ r v xy) (p.tree r).depth v (List.ofFn bits) (by simp),
    FrontierLocation.take_first_eq_hit (halt p μ r v xy) (p.tree r).depth v (List.ofFn bits) (by simp),
    StoppedAzuma.outcome_eq_hit]

theorem trial_acceptance (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β : ℝ) (hβ : β ≤ 1 / 8) (hsmooth : Smooth p β)
    (r : R) (v : List Bool) (xy : X × Y) (hr : Reached p μ r xy v)
    (t : ℝ) (ht : 0 < t) (bits : Candidate p r) :
    let d := trialData p μ r v β t ht
    let i := IndexedRejection.index d bits xy.1 xy.2
    let w := StoppedAzuma.finiteOutcome (p.tree r).depth (halt p μ r v xy) v bits
    d.aliceAccept xy.1 bits i = min 1 (mass (player .alice p μ r v xy) w /
      (t * mass (observer p μ r v xy) w)) ∧
    d.bobAccept xy.2 bits i = min 1 (mass (player .bob p μ r v xy) w /
      (t * mass (observer p μ r v xy) w)) := by
  let w := StoppedAzuma.finiteOutcome (p.tree r).depth (halt p μ r v xy) v bits
  have ha := player_likelihood .alice p μ β hβ hsmooth r v xy hr w
  have hb := player_likelihood .bob p μ β hβ hsmooth r v xy hr w
  dsimp only
  constructor
  · change min 1 (Real.exp (StoppedAzuma.incrementSum
      (fun s ↦ logIncrement (aliceKernel p μ r xy.1 s) (Prefix.Prior.observerNext p μ r s)) v
      ((List.ofFn bits).take (IndexedRejection.index (trialData p μ r v β t ht) bits xy.1 xy.2).val)) / t) = _
    rw [trial_index_prefix]
    change min 1 (Real.exp (StoppedAzuma.incrementSum _ v w.1) / t) = _
    change Real.exp (StoppedAzuma.incrementSum
      (fun s ↦ logIncrement (aliceKernel p μ r xy.1 s) (Prefix.Prior.observerNext p μ r s)) v w.1) =
      mass (player .alice p μ r v xy) w / mass (observer p μ r v xy) w at ha
    rw [ha]
    congr 1
    ring
  · change min 1 (Real.exp (StoppedAzuma.incrementSum
      (fun s ↦ logIncrement (bobKernel p μ r xy.2 s) (Prefix.Prior.observerNext p μ r s)) v
      ((List.ofFn bits).take (IndexedRejection.index (trialData p μ r v β t ht) bits xy.1 xy.2).val)) / t) = _
    rw [trial_index_prefix]
    change min 1 (Real.exp (StoppedAzuma.incrementSum _ v w.1) / t) = _
    change Real.exp (StoppedAzuma.incrementSum
      (fun s ↦ logIncrement (bobKernel p μ r xy.2 s) (Prefix.Prior.observerNext p μ r s)) v w.1) =
      mass (player .bob p μ r v xy) w / mass (observer p μ r v xy) w at hb
    rw [hb]
    congr 1
    ring

theorem trial_cost_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (β t : ℝ) (ht : 0 < t) :
    (IndexedRejection.protocol (trialData p μ r v β t ht)).cost ≤
      2 * Nat.clog 2 ((p.tree r).depth + 1) + 2 :=
  IndexedRejection.cost_le _

noncomputable def trialDecode (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (v : Candidate p r × List Bool) : Option (List Bool) :=
  (IndexedRejection.decode (p.tree r).depth v).map (fun z ↦ (List.ofFn z.1).take z.2.val)

/-- The actual protocol, including its input-independent public proposal,
local stopping-index exchange, and two private acceptance bits, implements
exactly the clipped rejection trial on the concrete frontier. -/
theorem trial_decoded_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β : ℝ) (hβ : β ≤ 1 / 8) (hsmooth : Smooth p β)
    (r : R) (v : List Bool) (xy : X × Y) (hr : Reached p μ r xy v)
    (t : ℝ) (ht : 0 < t) :
    ((IndexedRejection.protocol (trialData p μ r v β t ht)).viewLaw xy.1 xy.2).map (trialDecode p r) =
      (Rejection.attempt (observer p μ r v xy)
        (TwoPartyRejection.acceptWeight (observer p μ r v xy)
          (player .alice p μ r v xy) (player .bob p μ r v xy) t)
        (TwoPartyRejection.accept_nonneg _ _ _ t ht)
        (TwoPartyRejection.accept_le_one _ _ _ t ht)).map (Option.map Subtype.val) := by
  let d := trialData p μ r v β t ht
  let F := StoppedAzuma.finiteOutcome (p.tree r).depth (halt p μ r v xy) v
  let O := observer p μ r v xy
  let A := fun w ↦ min 1 (mass (player .alice p μ r v xy) w / (t * mass O w))
  let B := fun w ↦ min 1 (mass (player .bob p μ r v xy) w / (t * mass O w))
  have hA₀ (w) : 0 ≤ A w := le_min (by norm_num) (div_nonneg (mass_nonneg _ _) (mul_nonneg ht.le (mass_nonneg _ _)))
  have hB₀ (w) : 0 ≤ B w := le_min (by norm_num) (div_nonneg (mass_nonneg _ _) (mul_nonneg ht.le (mass_nonneg _ _)))
  have hA₁ (w) : A w ≤ 1 := min_le_left _ _
  have hB₁ (w) : B w ≤ 1 := min_le_left _ _
  let label : Option (Candidate p r × Fin ((p.tree r).depth + 1)) → Option (List Bool) :=
    Option.map (fun z ↦ (List.ofFn z.1).take z.2.val)
  let K (w : Alphabet p μ r v xy) : PMF (Option (List Bool)) :=
    (LocalRejection.coin (A w) (hA₀ w) (hA₁ w)).bind fun a ↦
      (LocalRejection.coin (B w) (hB₀ w) (hB₁ w)).map fun b ↦ if a && b then some w.1 else none
  have hbranch (bits : Candidate p r) :
      ((LocalRejection.coin (d.aliceAccept xy.1 bits (IndexedRejection.index d bits xy.1 xy.2))
        (d.alice_nonneg _ _ _) (d.alice_le_one _ _ _)).bind fun a ↦
          (LocalRejection.coin (d.bobAccept xy.2 bits (IndexedRejection.index d bits xy.1 xy.2))
            (d.bob_nonneg _ _ _) (d.bob_le_one _ _ _)).map fun b ↦
              if a && b then some (bits,IndexedRejection.index d bits xy.1 xy.2) else none).map label = K (F bits) := by
    have he := trial_acceptance p μ β hβ hsmooth r v xy hr t ht bits
    change d.aliceAccept xy.1 bits (IndexedRejection.index d bits xy.1 xy.2) = A (F bits) ∧
      d.bobAccept xy.2 bits (IndexedRejection.index d bits xy.1 xy.2) = B (F bits) at he
    rw [PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    simp only [he.1, he.2, K]
    congr 1
    funext a
    congr 1
    funext b
    cases a <;> cases b <;> simp [label, F, d, trial_index_prefix, StoppedAzuma.finiteOutcome]
  calc
    _ = d.proposal.bind (fun bits ↦ K (F bits)) := by
      have he : ((IndexedRejection.protocol d).viewLaw xy.1 xy.2).map (trialDecode p r) =
          (((IndexedRejection.protocol d).viewLaw xy.1 xy.2).map (IndexedRejection.decode _)).map label := by
        rw [PMF.map_comp]
        rfl
      rw [he, IndexedRejection.decoded_law, PMF.map_bind]
      exact congrArg (PMF.bind d.proposal) (funext hbranch)
    _ = O.bind K := by
      change d.proposal.bind (K ∘ F) = _
      rw [← PMF.bind_map]
      exact congrArg (fun q ↦ q.bind K) (candidateLaw_frontier p μ r v xy β)
    _ = _ := by
      have hh := congrArg (fun q ↦ q.map (Option.map Subtype.val))
        (LocalRejection.coinTrial_eq_attempt O A B hA₀ hA₁ hB₀ hB₁)
      have hweight : (fun w ↦ A w * B w) = TwoPartyRejection.acceptWeight
          (observer p μ r v xy) (player .alice p μ r v xy) (player .bob p μ r v xy) t := by
        funext w
        rfl
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, apply_ite,
        Option.map_some, Option.map_none] at hh
      simp only [hweight] at hh
      exact hh

noncomputable def leafIndex (p : Disjointness.Protocol X Y R SA SB) (r : R) (v : List Bool)
    (bits : Candidate p r) : Fin ((p.tree r).depth + 1) :=
  ⟨FrontierLocation.first (terminal p r) v (List.ofFn bits), by
    have hh := FrontierLocation.first_le (terminal p r) v (List.ofFn bits)
    simpa using Nat.lt_succ_of_le hh⟩

theorem indices_le_leaf (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (β t : ℝ) (ht : 0 < t) (xy : X × Y) (bits : Candidate p r) :
    (trialData p μ r v β t ht).aliceIndex bits xy.1 ≤ leafIndex p r v bits ∧
      (trialData p μ r v β t ht).bobIndex bits xy.2 ≤ leafIndex p r v bits := by
  constructor
  · apply FrontierLocation.first_mono
    intro s hs
    simp only [terminal, decide_eq_true_eq] at hs
    simp [aliceStop, hs]
  · apply FrontierLocation.first_mono
    intro s hs
    simp only [terminal, decide_eq_true_eq] at hs
    simp [bobStop, hs]

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem leaf_index_terminal (p : Disjointness.Protocol X Y R SA SB) (r : R) (v : List Bool)
    (bits : Candidate p r) : terminal p r (v ++ (List.ofFn bits).take (leafIndex p r v bits).val) = true := by
  have hh := StoppingFrontier.halt_hit (p.tree r).depth (terminal p r) v (List.ofFn bits) (by simp)
    (terminal_depth p r _ (by simp))
  rw [← FrontierLocation.take_first_eq_hit (terminal p r) (p.tree r).depth v (List.ofFn bits) (by simp)] at hh
  exact hh

/-- Index messages occur exactly when the proposal reaches a nonterminal
frontier. The final public leaf is decoded without transmitting its index. -/
theorem index_messages_iff (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (v : List Bool) (β t : ℝ) (ht : 0 < t) (xy : X × Y) (bits : Candidate p r) :
    ¬((trialData p μ r v β t ht).aliceIndex bits xy.1 = leafIndex p r v bits ∧
      (trialData p μ r v β t ht).bobIndex bits xy.2 = leafIndex p r v bits) ↔
      Prefix.Tree.speaker (p.tree r) (v ++ StoppedAzuma.outcome (p.tree r).depth (halt p μ r v xy) v bits) ≠ none := by
  let d := trialData p μ r v β t ht
  let i := IndexedRejection.index d bits xy.1 xy.2
  have hbounds := indices_le_leaf p μ r v β t ht xy bits
  have hi : i ≤ leafIndex p r v bits := (min_le_left _ _).trans hbounds.1
  have hiff : (d.aliceIndex bits xy.1 = leafIndex p r v bits ∧ d.bobIndex bits xy.2 = leafIndex p r v bits) ↔
      i = leafIndex p r v bits := by
    constructor
    · rintro ⟨ha,hb⟩; simp [i, IndexedRejection.index, ha,hb]
    · intro he
      have ha : leafIndex p r v bits ≤ d.aliceIndex bits xy.1 := by rw [← he]; exact min_le_left _ _
      have hb : leafIndex p r v bits ≤ d.bobIndex bits xy.2 := by rw [← he]; exact min_le_right _ _
      exact ⟨le_antisymm hbounds.1 ha, le_antisymm hbounds.2 hb⟩
  rw [hiff, ← trial_index_prefix p μ r v xy β t ht bits]
  by_cases he : i = leafIndex p r v bits
  · have hh := leaf_index_terminal p r v bits
    simp only [terminal, decide_eq_true_eq] at hh
    simp [he, hh, i, d]
  · have hlt : i.val < (leafIndex p r v bits).val := by exact_mod_cast lt_of_le_of_ne hi he
    have hh := FrontierLocation.not_halt_before_first (terminal p r) v (List.ofFn bits) i.val hlt
    have hn : Prefix.Tree.speaker (p.tree r) (v ++ (List.ofFn bits).take i.val) ≠ none := by
      simpa [terminal] using hh
    simpa [he, i, d] using hn

noncomputable def lazyTrialDecode (p : Disjointness.Protocol X Y R SA SB) (r : R) (v : List Bool)
    (z : Candidate p r × List Bool) : Option (List Bool) :=
  (LazyIndexedRejection.decode (leafIndex p r v) z).map (fun z ↦ (List.ofFn z.1).take z.2.val)

theorem lazy_trial_law (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β : ℝ) (hβ : β ≤ 1 / 8) (hsmooth : Smooth p β)
    (r : R) (v : List Bool) (xy : X × Y) (hr : Reached p μ r xy v)
    (t : ℝ) (ht : 0 < t) :
    ((LazyIndexedRejection.protocol (trialData p μ r v β t ht) (leafIndex p r v)).viewLaw xy.1 xy.2).map
      (lazyTrialDecode p r v) =
      (Rejection.attempt (observer p μ r v xy)
        (TwoPartyRejection.acceptWeight (observer p μ r v xy) (player .alice p μ r v xy) (player .bob p μ r v xy) t)
        (TwoPartyRejection.accept_nonneg _ _ _ t ht) (TwoPartyRejection.accept_le_one _ _ _ t ht)).map (Option.map Subtype.val) := by
  have hh := congrArg (fun q ↦ q.map (Option.map (fun z ↦ (List.ofFn z.1).take z.2.val)))
    (LazyIndexedRejection.decoded_law (trialData p μ r v β t ht) (leafIndex p r v) xy.1 xy.2)
  simp only [PMF.map_comp, Function.comp_def] at hh
  exact hh.trans (trial_decoded_law p μ β hβ hsmooth r v xy hr t ht)

end BBCR.LikelihoodFrontier
