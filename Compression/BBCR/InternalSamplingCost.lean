module

public import BBCR.InternalSampling

/-! Exact expected number of common-threshold mistakes, with the square-root
internal-information bound and its Markov truncation estimate. -/

@[expose] public section

open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR.InternalSampling

open Prefix FiniteAzuma InternalPrediction

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB]

noncomputable local instance : DecidableEq (X ⊕ Y) := Classical.decEq _

noncomputable def flag (C : ℕ) (s : List Bool) (xy : X × Y) (row : Row X Y C) : ℝ :=
  if read C row s (.inl xy.1) ≠ read C row s (.inr xy.2) then 1 else 0

noncomputable def mistakes (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (C : ℕ) : (n : ℕ) → Tape X Y C n → List Bool → ℝ
  | 0, _, _ => 0
  | n + 1, tape, s => if LikelihoodFrontier.terminal p r s then 0 else
      flag C s xy (tape 0) + mistakes p r xy C n (Fin.tail tape)
        (s ++ [ownerBit p r xy C s (tape 0)])

omit [Fintype X] [Fintype Y] [Fintype SA] [Fintype SB] in
theorem mistakes_nonneg (p : Disjointness.Protocol X Y R SA SB) (r : R)
    (xy : X × Y) (C n : ℕ) (tape : Tape X Y C n) (s : List Bool) :
    0 ≤ mistakes p r xy C n tape s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [mistakes]
    split_ifs
    · exact le_rfl
    · exact add_nonneg (by unfold flag; split_ifs <;> norm_num) (ih _ _)

theorem flag_expect (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (C : ℕ) (s : List Bool) (hs : s.length ≤ C) :
    expect (rowLaw p μ r C) (flag C s xy) = variation (alice p μ r xy.1 s) (bob p μ r xy.2 s) := by
  have he : (rowLaw p μ r C).map (fun row ↦ read C row s) = coupledNode p μ r s := by
    simpa only [rowLaw,read,dite_eq_left hs] using
      ProtocolIteration.pi_eval (fun t : BoundedHistory.State C ↦ coupledNode p μ r t.1) ⟨s,hs⟩
  have hp := probability_map (rowLaw p μ r C) (fun row ↦ read C row s)
    (fun row ↦ row (.inl xy.1) ≠ row (.inr xy.2))
  rw [he,coupledNode_mistake] at hp
  rw [hp]
  unfold expect flag probability
  apply Finset.sum_congr rfl
  intro row _
  by_cases hh : read C row s (.inl xy.1) = read C row s (.inr xy.2) <;> simp [hh]

noncomputable def disagreement (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (s : List Bool) : ℝ :=
  variation (alice p μ r xy.1 s) (bob p μ r xy.2 s)

theorem mistakes_expect (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (C n : ℕ) (s : List Bool) (hs : s.length + n ≤ C) :
    expect (tapeLaw p μ r C n) (fun tape ↦ mistakes p r xy C n tape s) =
      KernelPotential.future (LikelihoodFrontier.terminal p r) (ProtocolFrontier.targetKernel p μ r xy)
        (disagreement p μ r xy) n s := by
  induction n generalizing s with
  | zero => simp [mistakes,KernelPotential.future,expect]
  | succ n ih =>
    cases hn : LikelihoodFrontier.terminal p r s with
    | true => simp [mistakes,KernelPotential.future,hn,expect]
    | false =>
      rw [tapeLaw_succ,expect_bind]
      simp_rw [expect_map]
      have he (row : Row X Y C) : expect (tapeLaw p μ r C n)
          (fun rest ↦ mistakes p r xy C (n + 1) (Fin.cons row rest) s) =
          flag C s xy row + KernelPotential.future (LikelihoodFrontier.terminal p r)
            (ProtocolFrontier.targetKernel p μ r xy) (disagreement p μ r xy) n
            (s ++ [ownerBit p r xy C s row]) := by
        simp only [mistakes,hn,Bool.false_eq_true,ite_false,Fin.cons_zero,Fin.tail_cons,
          expect_add,expect_const]
        rw [ih _ (by simp only [List.length_append,List.length_singleton]; omega)]
      simp_rw [he]
      rw [expect_add,flag_expect p μ r xy C s (by omega)]
      rw [← expect_map (rowLaw p μ r C) (ownerBit p r xy C s)
        (fun b ↦ KernelPotential.future (LikelihoodFrontier.terminal p r)
          (ProtocolFrontier.targetKernel p μ r xy) (disagreement p μ r xy) n (s ++ [b])),
        ownerBit_law p μ r xy C s (by omega) hn]
      simp only [KernelPotential.future,hn,Bool.false_eq_true,ite_false,disagreement]

variable [Fintype R]

theorem pathSum_eq_disagreement (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) (ω : SA × SB) :
    StoppedAzuma.pathSum (disagreement p μ r xy) [] (Experiment.transcript p r xy.1 xy.2 ω) =
      pathDisagreement p μ r p.cost (xy,ω) := by
  rw [StoppedAzuma.pathSum_range]
  simp only [List.nil_append]
  let T := Experiment.transcript p r xy.1 xy.2 ω
  have hlen : T.length ≤ p.cost := (Disjointness.Tree.run_length_le_depth _ _ _).trans (p.depth_le_cost r)
  change (∑ j ∈ Finset.range T.length, disagreement p μ r xy (T.take j)) =
    ∑ j ∈ Finset.range p.cost, disagreement p μ r xy (T.take j)
  rw [show p.cost = T.length + (p.cost - T.length) by omega,Finset.sum_range_add]
  rw [show (∑ j ∈ Finset.range (p.cost - T.length), disagreement p μ r xy (T.take (T.length + j))) = 0 from ?_,add_zero]
  apply Finset.sum_eq_zero
  intro j _
  have hstop := (Tree.speaker_take_eq_none_iff (p.tree r) (xy.1,ω.1) (xy.2,ω.2) (T.length + j)).mpr
    (by change T.length ≤ T.length + j; omega)
  change Tree.speaker (p.tree r) (T.take (T.length + j)) = none at hstop
  simp [disagreement,alice,bob,hstop,variation]

theorem mistakes_expect_root (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (xy : X × Y) :
    expect (tapeLaw p μ r p.cost p.cost) (fun tape ↦ mistakes p r xy p.cost p.cost tape []) =
      expect (Experiment.privateSeeds p) (fun ω ↦ pathDisagreement p μ r p.cost (xy,ω)) := by
  rw [mistakes_expect p μ r xy p.cost p.cost [] (by simp),KernelPotential.future_eq_expect,
    leaf_law,expect_map]
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  exact pathSum_eq_disagreement p μ r xy ω

theorem average_mistakes (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    (∑ r, mass p.publicLaw r * expect μ (fun xy ↦
      expect (tapeLaw p μ r p.cost p.cost) (fun tape ↦ mistakes p r xy p.cost p.cost tape []))) =
      expectedDisagreement p μ := by
  simp_rw [mistakes_expect_root]
  simp only [expectedDisagreement,Prior.execution_expect]

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

theorem average_mistakes_le (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    (∑ r, mass p.publicLaw r * expect μ (fun xy ↦
      expect (tapeLaw p μ r p.cost p.cost) (fun tape ↦ mistakes p r xy p.cost p.cost tape []))) ≤
      Real.sqrt ((p.cost : ℝ) * internalInformation p μ) := by
  rw [average_mistakes]
  exact expectedDisagreement_le_sqrt p μ

theorem mistakes_tail (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (L : ℝ) (hL : 0 < L) :
    (∑ r, mass p.publicLaw r * expect μ (fun xy ↦
      probability (tapeLaw p μ r p.cost p.cost) (fun tape ↦ L ≤ mistakes p r xy p.cost p.cost tape []))) ≤
      Real.sqrt ((p.cost : ℝ) * internalInformation p μ) / L := by
  have hb (r : R) (xy : X × Y) := probability_le_expect_div (tapeLaw p μ r p.cost p.cost)
    (fun tape ↦ mistakes p r xy p.cost p.cost tape []) L hL (fun tape _ ↦ mistakes_nonneg p r xy _ _ tape [])
  calc
    _ ≤ ∑ r, mass p.publicLaw r * expect μ (fun xy ↦
        expect (tapeLaw p μ r p.cost p.cost) (fun tape ↦ mistakes p r xy p.cost p.cost tape []) / L) := by
      apply Finset.sum_le_sum
      intro r _
      apply mul_le_mul_of_nonneg_left _ (mass_nonneg _ _)
      exact Finset.sum_le_sum fun xy _ ↦ mul_le_mul_of_nonneg_left (hb r xy) (mass_nonneg μ xy)
    _ = (∑ r, mass p.publicLaw r * expect μ (fun xy ↦
        expect (tapeLaw p μ r p.cost p.cost) (fun tape ↦ mistakes p r xy p.cost p.cost tape []))) / L := by
      simp only [expect_div,mul_div_assoc,Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (average_mistakes_le p μ) hL.le

end BBCR.InternalSampling
