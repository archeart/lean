module

public import BBCR.ProtocolIteration
public import BBCR.KernelCoupling

/-! Public mixtures of protocol families with dependent finite seed types.
Private tables retain their independence from the selected public branch. -/

@[expose] public section

open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR.ProtocolFamily

variable {X Y I : Type} {R SA SB : I → Type} [Fintype I]
  [∀ i, Fintype (R i)] [∀ i, Fintype (SA i)] [∀ i, Fintype (SB i)]

theorem dependent_pi_eval {T : I → Type} [∀ i, Fintype (T i)] (q : (i : I) → PMF (T i)) (i : I) :
    (pi q).map (fun row ↦ row i) = q i := by
  let : (i : I) → MeasurableSpace (T i) := fun _ ↦ ⊤
  let : (i : I) → DiscreteMeasurableSpace (T i) := fun _ ↦ ⟨fun _ ↦ trivial⟩
  exact pi_map_eval q i

noncomputable def protocol (w : PMF I) (p : (i : I) → Protocol X Y (R i) (SA i) (SB i)) :
    Protocol X Y (Σ i, R i) ((i : I) → SA i) ((i : I) → SB i) where
  publicLaw := w.bind (fun i ↦ (p i).publicLaw.map (Sigma.mk i))
  aliceLaw := pi (fun i ↦ (p i).aliceLaw)
  bobLaw := pi (fun i ↦ (p i).bobLaw)
  tree z := ((p z.1).tree z.2).comap (fun a ↦ (a.1,a.2 z.1)) (fun b ↦ (b.1,b.2 z.1))

theorem cost_le (w : PMF I) (p : (i : I) → Protocol X Y (R i) (SA i) (SB i))
    (Q : ℕ) (hQ : ∀ i, (p i).cost ≤ Q) : (protocol w p).cost ≤ Q := by
  apply Finset.sup_le
  intro z _
  exact (Disjointness.Tree.depth_comap _ _ _).le.trans
    ((Finset.le_sup (f := fun r ↦ ((p z.1).tree r).depth) (Finset.mem_univ z.2)).trans (hQ z.1))

variable {A : Type} [Fintype A]

omit [∀ i, Fintype (R i)] [Fintype A] in
theorem decoded_law (w : PMF I) (p : (i : I) → Protocol X Y (R i) (SA i) (SB i))
    (decode : (i : I) → R i × List Bool → A) (x : X) (y : Y) :
    ((protocol w p).viewLaw x y).map (fun v ↦ decode v.1.1 (v.1.2,v.2)) =
      w.bind (fun i ↦ ((p i).viewLaw x y).map (decode i)) := by
  have hbranch (i : I) (r : R i) :
      ((pi (fun i ↦ (p i).aliceLaw)).bind fun ap ↦
        (pi (fun i ↦ (p i).bobLaw)).map fun bp ↦
          decode i (r,(((p i).tree r).run (x,ap i) (y,bp i)).1)) =
      ((p i).aliceLaw.bind fun a ↦ (p i).bobLaw.map fun b ↦
        decode i (r,(((p i).tree r).run (x,a) (y,b)).1)) := by
    have hae := dependent_pi_eval (fun j ↦ (p j).aliceLaw) i
    have hbe := dependent_pi_eval (fun j ↦ (p j).bobLaw) i
    rw [← hae, ← hbe, PMF.bind_map]
    simp only [PMF.map_comp, Function.comp_def]
  simp only [Protocol.viewLaw, Protocol.seedLaw, protocol, PMF.map_comp, PMF.map_bind,
    PMF.bind_bind, PMF.bind_map, Function.comp_def, Tree.run_comap]
  congr 1
  funext i
  congr 1
  funext r
  exact hbranch i r

end BBCR.ProtocolFamily

namespace BBCR

variable {I A : Type*} [Fintype I] [Fintype A]

theorem variation_bind_le (w : PMF I) (K L : I → PMF A) :
    variation (w.bind K) (w.bind L) ≤ ∑ i, mass w i * variation (K i) (L i) := by
  have hh : (∑ a, |mass (w.bind K) a - mass (w.bind L) a|) ≤
      ∑ i, mass w i * ∑ a, |mass (K i) a - mass (L i) a| := by
    simp_rw [Disjointness.Channel.mass_bind, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ a, ∑ i, |mass w i * mass (K i) a - mass w i * mass (L i) a| :=
        Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        simp only [← mul_sub, abs_mul, abs_of_nonneg (mass_nonneg w i), Finset.mul_sum]
  unfold variation
  apply (div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end BBCR
