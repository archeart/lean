module

public import Disjointness.ExecutionConditioning

/-! A finite alphabet for the actual public-seed/transcript view. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Disjointness.Protocol

variable {X Y R SA SB : Type*}

/-- The public seed together with a leaf path of its selected tree. -/
def View (p : Protocol X Y R SA SB) := Σ r : R, ↥(p.tree r).leafPaths

noncomputable instance viewFintype [Fintype R] (p : Protocol X Y R SA SB) : Fintype p.View :=
  inferInstanceAs (Fintype (Σ r : R, ↥(p.tree r).leafPaths))

instance viewMeasurableSpace (p : Protocol X Y R SA SB) : MeasurableSpace p.View := ⊤
instance viewDiscreteMeasurableSpace (p : Protocol X Y R SA SB) : DiscreteMeasurableSpace p.View :=
  ⟨fun _ ↦ trivial⟩

def forgetView (p : Protocol X Y R SA SB) (v : p.View) : R × List Bool := (v.1, v.2.1)

theorem forgetView_injective (p : Protocol X Y R SA SB) : Function.Injective p.forgetView := by
  rintro ⟨r, t, ht⟩ ⟨r', t', ht'⟩ h
  cases h
  rfl

def runView (p : Protocol X Y R SA SB) (x : X) (y : Y) (s : R × (SA × SB)) : p.View :=
  ⟨s.1, ⟨((p.tree s.1).run (x, s.2.1) (y, s.2.2)).1, Tree.run_mem_leafPaths _ _ _⟩⟩

noncomputable def finiteViewLaw (p : Protocol X Y R SA SB) (x : X) (y : Y) : PMF p.View :=
  p.seedLaw.map (p.runView x y)

theorem finiteViewLaw_map (p : Protocol X Y R SA SB) (x : X) (y : Y) :
    (p.finiteViewLaw x y).map p.forgetView = p.viewLaw x y := by
  rw [finiteViewLaw, PMF.map_comp]
  rfl

theorem finiteViewLaw_apply (p : Protocol X Y R SA SB) (x : X) (y : Y) (v : p.View) :
    p.finiteViewLaw x y v = p.viewLaw x y (p.forgetView v) := by
  classical
  rw [← finiteViewLaw_map, PMF.map_apply]
  have he (a : p.View) : p.forgetView v = p.forgetView a ↔ v = a :=
    p.forgetView_injective.eq_iff
  simp only [he, tsum_ite_eq']

theorem finiteViewLaw_rectangle [Fintype SA] [Fintype SB]
    (p : Protocol X Y R SA SB) (x x' : X) (y y' : Y) (v : p.View) :
    p.finiteViewLaw x y v * p.finiteViewLaw x' y' v =
      p.finiteViewLaw x y' v * p.finiteViewLaw x' y v := by
  simp only [finiteViewLaw_apply, forgetView, viewLaw_factorization]
  ring

def viewOutput (p : Protocol X Y R SA SB) (v : p.View) : Bool :=
  ((p.tree v.1).decode v.2.1).getD false

@[simp] theorem viewOutput_runView (p : Protocol X Y R SA SB) (x : X) (y : Y)
    (s : R × (SA × SB)) :
    p.viewOutput (p.runView x y s) = ((p.tree s.1).run (x, s.2.1) (y, s.2.2)).2 := by
  simp [viewOutput, runView, Tree.decode_run]

theorem finiteViewLaw_output (p : Protocol X Y R SA SB) (x : X) (y : Y) :
    (p.finiteViewLaw x y).map p.viewOutput = p.outputLaw x y := by
  rw [finiteViewLaw, PMF.map_comp]
  simp only [Function.comp_def, viewOutput_runView, outputLaw]

end Disjointness.Protocol
