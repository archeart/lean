module

public import Disjointness.ReachableCost
public import Mathlib.Data.Fintype.Sum

/-! Arbitrary probability spaces of random tapes, normalized by their finite
bounded deterministic communication behavior. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Disjointness.BoundedTree

/-- A finite description of all local deterministic behaviors using at most `c` bits. -/
def Code (X Y : Type) : ℕ → Type
  | 0 => Bool
  | c + 1 => Bool ⊕ (((X → Bool) × Code X Y c × Code X Y c) ⊕
      ((Y → Bool) × Code X Y c × Code X Y c))

noncomputable instance codeFintype (X Y : Type) [Fintype X] [Fintype Y] :
    (c : ℕ) → Fintype (Code X Y c)
  | 0 => inferInstanceAs (Fintype Bool)
  | c + 1 => by
      classical
      letI : Fintype (Code X Y c) := codeFintype X Y c
      exact inferInstanceAs (Fintype (Bool ⊕ (((X → Bool) × Code X Y c × Code X Y c) ⊕
        ((Y → Bool) × Code X Y c × Code X Y c))))

instance {X Y : Type} {c : ℕ} : MeasurableSpace (Code X Y c) := ⊤
instance {X Y : Type} {c : ℕ} : DiscreteMeasurableSpace (Code X Y c) := ⟨fun _ ↦ trivial⟩

def toTree {X Y : Type} : {c : ℕ} → Code X Y c → Tree X Y
  | 0, b => .leaf b
  | _ + 1, .inl b => .leaf b
  | _ + 1, .inr (.inl (q,z,o)) => .alice q (toTree z) (toTree o)
  | _ + 1, .inr (.inr (q,z,o)) => .bob q (toTree z) (toTree o)

theorem depth_le {X Y : Type} {c : ℕ} (t : Code X Y c) : (toTree t).depth ≤ c := by
  induction c with
  | zero => simp [toTree, Tree.depth]
  | succ c ih =>
    rcases t with b | (⟨q,z,o⟩ | ⟨q,z,o⟩) <;> simp [toTree, Tree.depth, ih]

/-- Encode a tree by its behavior truncated at the communication bound. -/
def encode {X Y : Type} : (c : ℕ) → Tree X Y → Code X Y c
  | 0, .leaf b => b
  | 0, .alice _ _ _ => false
  | 0, .bob _ _ _ => false
  | _c + 1, .leaf b => .inl b
  | c + 1, .alice q z o => .inr (.inl (q,encode c z,encode c o))
  | c + 1, .bob q z o => .inr (.inr (q,encode c z,encode c o))

theorem toTree_encode {X Y : Type} (c : ℕ) (t : Tree X Y) :
    toTree (encode c t) = t.truncate c := by
  induction c generalizing t with
  | zero => cases t <;> rfl
  | succ c ih => cases t <;> simp [encode, toTree, Tree.truncate, ih]

/-- A distribution on bounded behaviors is an actual protocol with one public
seed and unused singleton private seeds. -/
noncomputable def protocol {X Y : Type} [Fintype X] [Fintype Y] {c : ℕ}
    (w : PMF (Code X Y c)) : Protocol X Y (Code X Y c) Unit Unit where
  publicLaw := w
  aliceLaw := PMF.pure ()
  bobLaw := PMF.pure ()
  tree t := (toTree t).comap Prod.fst Prod.fst

theorem protocol_cost_le {X Y : Type} [Fintype X] [Fintype Y] {c : ℕ}
    (w : PMF (Code X Y c)) : (protocol w).cost ≤ c := by
  apply Finset.sup_le
  intro t _
  simpa [protocol] using depth_le t

theorem protocol_outputLaw {X Y : Type} [Fintype X] [Fintype Y] {c : ℕ}
    (w : PMF (Code X Y c)) (x : X) (y : Y) :
    (protocol w).outputLaw x y = w.map (fun t ↦ ((toTree t).run x y).2) := by
  simp [Protocol.outputLaw, Protocol.seedLaw, protocol,
    Function.comp_def, ← PMF.bind_pure_comp]

end Disjointness.BoundedTree

namespace Disjointness

/-- An arbitrary random-tape space chooses a finite bounded deterministic behavior.
The probability space may be atomless; no finiteness assumption on tapes is made. -/
theorem random_tape_disjointness_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n c : ℕ}
    (behavior : Ω → BoundedTree.Code (Bits n) (Bits n) c) (hm : Measurable behavior)
    (hc : ∀ x y, μ.real {ω | ((BoundedTree.toTree (behavior ω)).run x y).2 ≠ disj x y} ≤ 1 / 3) :
    lowerBoundConstant * (n : ℝ) ≤ (c : ℝ) := by
  let ν := μ.map behavior
  have : IsProbabilityMeasure ν := inferInstance
  let w := ν.toPMF
  have hw : w.toMeasure = ν := Measure.toPMF_toMeasure ν
  have hcorrect : (BoundedTree.protocol w).Correct disj (1 / 3) := by
    intro x y
    rw [Protocol.error, BoundedTree.protocol_outputLaw]
    have he : (w.map (fun t ↦ ((BoundedTree.toTree t).run x y).2)) (!(disj x y)) =
        μ {ω | ((BoundedTree.toTree (behavior ω)).run x y).2 ≠ disj x y} := by
      rw [← PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
        ← PMF.toMeasure_map _ _ .of_discrete, Measure.map_apply .of_discrete (.singleton _), hw]
      rw [Measure.map_apply hm .of_discrete]
      congr 1
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      cases disj x y <;> cases ((BoundedTree.toTree (behavior ω)).run x y).2 <;> decide
    rw [he]
    exact hc x y
  exact (disjointness_lower_bound _ hcorrect).trans
    (by exact_mod_cast BoundedTree.protocol_cost_le w)

/-- Random tapes may choose trees with unreachable deep branches. Encoding at
an actual execution-length bound preserves correctness and gives a finite
public-seed protocol with the same input/output distribution. -/
theorem random_tree_disjointness_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (trees : Ω → Tree (Bits n) (Bits n)) (c : ℕ)
    (hm : Measurable (fun ω ↦ BoundedTree.encode c (trees ω)))
    (hlen : ∀ ω x y, ((trees ω).run x y).1.length ≤ c)
    (hc : ∀ x y, μ.real {ω | ((trees ω).run x y).2 ≠ disj x y} ≤ 1 / 3) :
    lowerBoundConstant * (n : ℝ) ≤ (c : ℝ) := by
  apply random_tape_disjointness_lower_bound μ (fun ω ↦ BoundedTree.encode c (trees ω)) hm
  intro x y
  have he (ω : Ω) : (BoundedTree.toTree (BoundedTree.encode c (trees ω))).run x y =
      (trees ω).run x y := by
    rw [BoundedTree.toTree_encode]
    exact Tree.run_truncate c (trees ω) x y (hlen ω x y)
  simpa only [he] using hc x y

end Disjointness
