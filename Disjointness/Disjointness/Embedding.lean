module

public import Disjointness.LocalRandomization
public import Disjointness.ProductReplacement

/-! Actual AND protocols obtained by private disjoint padding of a DISJ protocol. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Disjointness

open FiniteLaw Hellinger Channel

namespace Switch

/-- Insert a given coordinate pair into a pair of padding vectors. -/
def fill {n : ℕ} (i : Fin n) (xy : Bool × Bool) (z : Bits n × Bits n) : Bits n × Bits n :=
  (Function.update z.1 i xy.1, Function.update z.2 i xy.2)

theorem disj_fill {n : ℕ} (i : Fin n) (d : Bits n) (xy : Bool × Bool)
    (z : Bits n × Bits n) (hz : inputLaw d z ≠ 0) :
    disj (fill i xy z).1 (fill i xy z).2 = !(xy.1 && xy.2) := by
  have hs : (d,z) ∈ (law n).support := mul_ne_zero (switches_pos d) hz
  have hd := disj_of_mem_support hs
  simp only [disj, decide_eq_true_eq] at hd
  have he : (∀ j, (fill i xy z).1 j = false ∨ (fill i xy z).2 j = false) ↔
      xy.1 = false ∨ xy.2 = false := by
    constructor
    · intro h
      simpa [fill] using h i
    · intro h j
      by_cases hj : j = i
      · subst j
        simpa [fill] using h
      · simpa [fill, Function.update_of_ne hj] using hd j
  unfold disj
  simp only [he]
  rcases xy with ⟨a,b⟩
  cases a <;> cases b <;> decide

end Switch

namespace Protocol

variable {n : ℕ} {R SA SB : Type*} [Fintype R] [Fintype SA] [Fintype SB]

/-- The switch vector `d` fixes only the padding laws. The actual AND input is
inserted at `i`, replacing the private padding there, and the DISJ answer is negated. -/
noncomputable def embed (p : Protocol (Bits n) (Bits n) R SA SB) (i : Fin n) (d : Bits n) :
    Protocol Bool Bool R (Bits n × SA) (Bits n × SB) :=
  p.localRandomize (Switch.aliceLaw d) (Switch.bobLaw d)
    (fun x a ↦ Function.update a i x) (fun y b ↦ Function.update b i y) Bool.not

@[simp] theorem embed_cost (p : Protocol (Bits n) (Bits n) R SA SB) (i : Fin n) (d : Bits n) :
    (p.embed i d).cost = p.cost := localRandomize_cost ..

theorem embed_outputLaw (p : Protocol (Bits n) (Bits n) R SA SB)
    (i : Fin n) (d : Bits n) (x y : Bool) :
    (p.embed i d).outputLaw x y = (Switch.inputLaw d).bind
      (fun z ↦ (p.outputLaw (Switch.fill i (x,y) z).1 (Switch.fill i (x,y) z).2).map Bool.not) :=
  localRandomize_outputLaw ..

/-- Every AND input is covered, including the intersecting corner. -/
theorem embed_correct (p : Protocol (Bits n) (Bits n) R SA SB)
    (hc : p.Correct disj (1 / 3)) (i : Fin n) (d : Bits n) :
    (p.embed i d).Correct Bool.and (1 / 3) := by
  have hn (q : PMF Bool) (b : Bool) : mass (q.map Bool.not) (!b) = mass q b := by
    cases b <;> simp [mass, PMF.map_apply, tsum_fintype]
  intro x y
  change mass ((p.embed i d).outputLaw x y) (!(x && y)) ≤ 1 / 3
  rw [embed_outputLaw, mass_bind]
  simp_rw [hn]
  calc
    _ ≤ ∑ z, mass (Switch.inputLaw d) z * (1 / 3) := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : Switch.inputLaw d z = 0
      · simp [mass, hz]
      · have h := hc (Switch.fill i (x,y) z).1 (Switch.fill i (x,y) z).2
        rw [error, Switch.disj_fill i d (x,y) z hz, Bool.not_not] at h
        exact mul_le_mul_of_nonneg_left h (mass_nonneg _ _)
    _ = 1 / 3 := by rw [← Finset.sum_mul, sum_mass, one_mul]

end Protocol
end Disjointness
