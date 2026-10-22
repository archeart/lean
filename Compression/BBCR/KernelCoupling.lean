module

public import BBCR.KernelPotential

/-! Approximation by a continuation kernel which is already exact on completed
states, and contraction under deterministic public decoding. -/

@[expose] public section

open Disjointness Disjointness.Hellinger Disjointness.FiniteLaw
open scoped Classical

namespace BBCR

variable {S A B : Type*} [Fintype S] [Fintype A] [Fintype B]

omit [Fintype S] [Fintype B] in
theorem variation_triangle (p q r : PMF A) : variation p r ≤ variation p q + variation q r := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ abs_sub_le (mass p a) (mass q a) (mass r a))
  simp only [Finset.sum_add_distrib] at hh
  unfold variation
  linarith

omit [Fintype S] in
theorem variation_map_le (p q : PMF A) (f : A → B) : variation (p.map f) (q.map f) ≤ variation p q := by
  unfold variation
  have hh : (∑ b, |mass (p.map f) b - mass (q.map f) b|) ≤ ∑ a, |mass p a - mass q a| := by
    simp_rw [mass_map_sum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ b, ∑ a, |(if f a = b then mass p a else 0) - (if f a = b then mass q a else 0)| :=
        Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        change (∑ b, |(if f a = b then mass p a else 0) - (if f a = b then mass q a else 0)|) = _
        have he (b : B) : |(if f a = b then mass p a else 0) - (if f a = b then mass q a else 0)| =
            if b = f a then |mass p a - mass q a| else 0 := by
          by_cases h : b = f a
          · simp [h]
          · simp [h, Ne.symm h]
        simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  linarith

omit [Fintype B] in
theorem probability_joint (w : PMF S) (K : S → PMF A) (E : S × A → Prop) :
    probability (joint w K) E = FiniteAzuma.expect w (fun s ↦ probability (K s) (fun a ↦ E (s,a))) := by
  unfold probability FiniteAzuma.expect
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mass, joint_apply, ENNReal.toReal_mul]
  split_ifs <;> ring

omit [Fintype B] in
theorem variation_completion_le (w : PMF S) (K : S → PMF A) (decode : S → A)
    (terminal : S → Prop) (hterminal : ∀ s, terminal s → K s = PMF.pure (decode s)) :
    variation (w.map decode) (w.bind K) ≤ probability w (fun s ↦ ¬terminal s) := by
  have hh := variation_map_le_disagreement (joint w K) (fun z ↦ decode z.1) Prod.snd
  have hfirst : (joint w K).map (fun z ↦ decode z.1) = w.map decode := by
    change (joint w K).map (decode ∘ Prod.fst) = _
    rw [← PMF.map_comp, joint_map_fst]
  rw [hfirst, Disjointness.Channel.joint_map_snd, probability_joint] at hh
  apply hh.trans
  unfold FiniteAzuma.expect probability
  apply Finset.sum_le_sum
  intro s _
  dsimp only
  change mass w s * probability (K s) (fun a ↦ decode s ≠ a) ≤ @ite ℝ (¬terminal s) (Classical.propDecidable _) (mass w s) 0
  by_cases hs : terminal s
  · rw [hterminal s hs]
    have hz : probability (PMF.pure (decode s)) (fun a ↦ decode s ≠ a) = 0 := by
      unfold probability
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : a = decode s
      · simp [ha]
      · simp [ha, mass]
    simp only [hz, hs, not_true_eq_false, ite_false, mul_zero, le_refl]
  · have hb := probability_le_one (K s) (fun a ↦ decode s ≠ a)
    simpa only [hs, not_false_eq_true, ite_true, mul_one] using mul_le_mul_of_nonneg_left hb (mass_nonneg w s)

end BBCR
