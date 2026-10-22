module

public import BBCR.SmoothingSmoothness
public import BBCR.PrefixAccounting

/-! Proposition 8.6 instantiated for actual smooth protocol kernels, their
observer mixtures, and local divergence along private-randomness execution. -/

@[expose] public section

open Disjointness Disjointness.Hellinger
open scoped Classical

namespace BBCR

theorem mixture_mass_mem {A B : Type*} [Fintype A] (w : PMF A) (K : A → PMF B)
    (l u : ℝ) (b : B) (hK : ∀ a, mass w a ≠ 0 → mass (K a) b ∈ Set.Icc l u) :
    mass (w.bind K) b ∈ Set.Icc l u := by
  rw [Disjointness.Channel.mass_bind]
  have hl := Finset.sum_le_sum (s := Finset.univ) (f := fun a ↦ mass w a * l)
    (g := fun a ↦ mass w a * mass (K a) b) (fun a _ ↦ by
      by_cases ha : mass w a = 0
      · simp [ha]
      · exact mul_le_mul_of_nonneg_left (hK a ha).1 (mass_nonneg w a))
  have hu := Finset.sum_le_sum (s := Finset.univ) (f := fun a ↦ mass w a * mass (K a) b)
    (g := fun a ↦ mass w a * u) (fun a _ ↦ by
      by_cases ha : mass w a = 0
      · simp [ha]
      · exact mul_le_mul_of_nonneg_left (hK a ha).2 (mass_nonneg w a))
  rw [← Finset.sum_mul, sum_mass, one_mul] at hl hu
  exact ⟨hl,hu⟩

variable {X Y R SA SB : Type} [Fintype SA] [Fintype SB]

theorem Smooth.next_mass_mem {p : Protocol X Y R SA SB} {β : ℝ} (hs : Smooth p β)
    (r : R) (x : X) (y : Y) (s : List Bool) (who : Prefix.Speaker)
    (howner : Prefix.Tree.speaker (p.tree r) s = some who)
    (hpos : 0 < Prefix.Protocol.reach p r x y s) (bit : Bool) :
    mass (Prefix.Protocol.next p r x y s) bit ∈ Set.Icc (1 / 2 - β) (1 / 2 + β) := by
  have ht := hs r x y s who howner hpos
  cases bit with
  | true => exact ht
  | false =>
    have he := sum_mass (Prefix.Protocol.next p r x y s)
    simp only [Fintype.sum_bool] at he
    constructor <;> linarith [ht.1, ht.2]

namespace Prefix.Prior

variable [Fintype X] [Fintype Y]

theorem observerNext_mass_mem (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β : ℝ) (hs : Smooth p β) (r : R) (s : List Bool) (who : Speaker)
    (howner : Tree.speaker (p.tree r) s = some who) (hpos : 0 < prefixMass p μ r s) (bit : Bool) :
    mass (observerNext p μ r s) bit ∈ Set.Icc (1 / 2 - β) (1 / 2 + β) := by
  apply mixture_mass_mem
  intro xy hxy
  exact hs.next_mass_mem r xy.1 xy.2 s who howner (posterior_support_reach_pos p μ r s hpos xy hxy) bit

theorem nodeDivergence_eq_next (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (r : R) (s : List Bool) (who : Speaker) (howner : Tree.speaker (p.tree r) s = some who)
    (hpos : 0 < prefixMass p μ r s) (xy : X × Y) (hxy : mass (posterior p μ r s) xy ≠ 0) :
    nodeDivergence p μ r s xy = divergence (Protocol.next p r xy.1 xy.2 s) (observerNext p μ r s) := by
  have hr := posterior_support_reach_pos p μ r s hpos xy hxy
  cases who with
  | alice => simp [nodeDivergence, aliceDivergence, bobDivergence, howner,
      Protocol.next_eq_alice p r xy.1 xy.2 s howner hr]
  | bob => simp [nodeDivergence, aliceDivergence, bobDivergence, howner,
      Protocol.next_eq_bob p r xy.1 xy.2 s howner hr]

/-- Actual local step divergence is between zero and `8β` in a beta-smooth
protocol, with all real-KL support obligations discharged on the posterior. -/
theorem nodeDivergence_mem (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 4) (hs : Smooth p β)
    (r : R) (s : List Bool) (hpos : 0 < prefixMass p μ r s)
    (xy : X × Y) (hxy : mass (posterior p μ r s) xy ≠ 0) :
    nodeDivergence p μ r s xy ∈ Set.Icc 0 (8 * β) := by
  refine ⟨nodeDivergence_nonneg p μ r s xy hpos hxy, ?_⟩
  cases howner : Tree.speaker (p.tree r) s with
  | none => simp [nodeDivergence, aliceDivergence, bobDivergence, howner, hβ₀]
  | some who =>
    rw [nodeDivergence_eq_next p μ r s who howner hpos xy hxy]
    apply smooth_divergence_le _ _ β hβ₀ hβ₁
    · intro bit
      exact (hs.next_mass_mem r xy.1 xy.2 s who howner
        (posterior_support_reach_pos p μ r s hpos xy hxy) bit).2
    · intro bit
      exact (observerNext_mass_mem p μ β hs r s who howner hpos bit).1

theorem reached_divergence_mem (p : Disjointness.Protocol X Y R SA SB) (μ : PMF (X × Y))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 4) (hs : Smooth p β)
    (r : R) (k : ℕ) (ω : Sample X Y SA SB) (hω : mass (execution p μ) ω ≠ 0) :
    nodeDivergence p μ r (history p r k ω) ω.1 ∈ Set.Icc 0 (8 * β) := by
  obtain ⟨hp,hxy⟩ := reached_posterior_support p μ r k ω hω
  exact nodeDivergence_mem p μ β hβ₀ hβ₁ hs r _ hp ω.1 hxy

end Prefix.Prior
end BBCR
