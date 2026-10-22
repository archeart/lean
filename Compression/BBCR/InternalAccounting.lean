module

public import BBCR.InternalInformationBridge
public import BBCR.LikelihoodBounds

/-! Exact internal information accounting along the original execution. The
local statistic conditions the observer on each receiver's actual input. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR.FiniteCondition

variable {A H : Type} [Fintype A] [Fintype H]

theorem sum_all_fibers (p : PMF A) (f : A → H) (g : H → A → ℝ) :
    (∑ h, mass (p.map f) h * ∑ a, mass (law p f h) a * g h a) =
      ∑ a, mass p a * g (f a) a := by
  simp only [Finset.mul_sum, ← mul_assoc, weighted_mass_law, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

omit [Fintype H] in
theorem own_fiber_support (p : PMF A) (f : A → H) (a : A) (ha : mass p a ≠ 0) :
    mass (law p f (f a)) a ≠ 0 := by
  have hh := weighted_mass_law p f (f a) a
  simp only [ite_true] at hh
  exact (mul_ne_zero_iff.mp (hh.trans_ne ha)).2

end BBCR.FiniteCondition

namespace BBCR.Prefix.Prior

open FiniteAzuma

variable {X Y R SA SB : Type} [Fintype X] [Fintype Y] [Fintype R] [Fintype SA] [Fintype SB]
  [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
  [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA]
  [MeasurableSpace SB] [DiscreteMeasurableSpace SB]

noncomputable def internalNodeDivergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (s : List Bool) (xy : X × Y) : ℝ :=
  nodeDivergence p (alicePrior μ xy.1) r s xy + nodeDivergence p (bobPrior μ xy.2) r s xy

noncomputable def internalPathDivergence (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (n : ℕ) (ω : Sample X Y SA SB) : ℝ :=
  pathDivergence p (alicePrior μ ω.1.1) r n ω + pathDivergence p (bobPrior μ ω.1.2) r n ω

omit [Fintype R] [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y] [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA] [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem internalPathDivergence_eq_sum (p : Disjointness.Protocol X Y R SA SB)
    (μ : PMF (X × Y)) (r : R) (n : ℕ) (ω : Sample X Y SA SB) :
    internalPathDivergence p μ r n ω = ∑ k ∈ Finset.range n,
      internalNodeDivergence p μ r (history p r k ω) ω.1 := by
  simp only [internalPathDivergence,internalNodeDivergence,pathDivergence,Finset.sum_add_distrib]

omit [Fintype R] [MeasurableSpace X] [DiscreteMeasurableSpace X]
  [MeasurableSpace Y] [DiscreteMeasurableSpace Y] [MeasurableSpace R] [DiscreteMeasurableSpace R]
  [MeasurableSpace SA] [DiscreteMeasurableSpace SA] [MeasurableSpace SB] [DiscreteMeasurableSpace SB] in
theorem execution_expect (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (g : Sample X Y SA SB → ℝ) :
    expect (execution p μ) g = expect μ (fun xy ↦ expect (Experiment.privateSeeds p) (fun ω ↦ g (xy,ω))) := by
  rw [execution,joint_eq_bind,expect_bind]
  simp only [expect_map]

variable {H : Type} [Fintype H]

/-- Conditioning on the receiver's input commutes with the full transcript
information accounting. No conditional fresh-seed hypothesis is introduced. -/
theorem expected_conditioned_path (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (f : X × Y → H) :
    (∑ r, mass p.publicLaw r * expect (execution p μ)
      (fun ω ↦ pathDivergence p (FiniteCondition.law μ f (f ω.1)) r p.cost ω)) =
      ∑ h, mass (μ.map f) h * externalInformation p (FiniteCondition.law μ f h) := by
  simp_rw [execution_expect]
  have he (r : R) := FiniteCondition.sum_all_fibers μ f
    (fun h xy ↦ expect (Experiment.privateSeeds p) (fun ω ↦ pathDivergence p (FiniteCondition.law μ f h) r p.cost (xy,ω)))
  change (∑ r, mass p.publicLaw r * ∑ xy, mass μ xy *
    (fun xy ↦ expect (Experiment.privateSeeds p) (fun ω ↦ pathDivergence p (FiniteCondition.law μ f (f xy)) r p.cost (xy,ω))) xy) = _
  simp_rw [← he]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [externalInformation_eq_public_average]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hh := expected_full_divergence p (FiniteCondition.law μ f h) r p.cost (p.depth_le_cost r)
  change expect (execution p (FiniteCondition.law μ f h)) _ = _ at hh
  rw [execution_expect] at hh
  rw [← hh]
  simp only [expect,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xy _
  apply Finset.sum_congr rfl
  intro ω _
  ring

omit [Fintype H] in
theorem expected_internal_path (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y)) :
    (∑ r, mass p.publicLaw r * expect (execution p μ) (internalPathDivergence p μ r p.cost)) =
      internalInformation p μ := by
  have ha := expected_conditioned_path p μ Prod.fst
  have hb := expected_conditioned_path p μ Prod.snd
  unfold internalPathDivergence
  simp_rw [expect_add,mul_add,Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) ha hb

end BBCR.Prefix.Prior
