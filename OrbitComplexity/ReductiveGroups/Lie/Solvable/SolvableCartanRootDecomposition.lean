import OrbitComplexity.ReductiveGroups.Lie.Solvable.SolvableRootSubset
import OrbitComplexity.ReductiveGroups.Lie.Roots.RootSpaceSubalgebraClosure
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Solvable Cartan Root Decomposition

A solvable subalgebra containing a Cartan subalgebra is stable under that
Cartan and decomposes into its root-space intersections. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L]
  (H S : LieSubalgebra K L) (hHS : H ≤ S)

/-- The subalgebra `S`, regarded as a submodule of the adjoint action
of its contained Cartan `H`. -/
def cartanStableSubmodule : LieSubmodule K H L :=
  { (S : Submodule K L) with
    lie_mem := fun {x _y} hy => S.lie_mem (hHS x.property) hy }

omit [CharZero K] [FiniteDimensional K L] in
/-- The equivalence is

```lean
x ∈ cartanStableSubmodule H S hHS ↔ x ∈ S
```
-/
@[simp] theorem mem_cartanStableSubmodule (x : L) :
    x ∈ cartanStableSubmodule H S hHS ↔ x ∈ S := Iff.rfl

variable [H.IsCartanSubalgebra] [IsTriangularizable K H L]

omit [CharZero K] in
/-- The Cartan-stable subalgebra is spanned by its intersections with
the generalized root spaces.  -/
theorem CartanStableSubmodule.eq_iSup_inf_rootSpace :
    cartanStableSubmodule H S hHS =
      ⨆ α : Weight K H L,
        cartanStableSubmodule H S hHS ⊓ rootSpace H α := by
  exact LieModule.eq_iSup_inf_genWeightSpace K H L
    (cartanStableSubmodule H S hHS)

variable [LieAlgebra.IsKilling K L]

/-- In the Killing case, every nonzero root-space component of `S` is
either absent or the entire one-dimensional root space. -/
theorem CartanStableSubmodule.eq_cartan_sup_contained_roots :
    cartanStableSubmodule H S hHS = H.toLieSubmodule ⊔
      ⨆ (α : H.root)
        (_ : rootSpace H α.val ≤ cartanStableSubmodule H S hHS),
        rootSpace H α.val := by
  let N := cartanStableSubmodule H S hHS
  have hHN : H.toLieSubmodule ≤ N := by
    intro x hx
    exact hHS hx
  refine le_antisymm ?_ (sup_le hHN (iSup₂_le fun _ hα => hα))
  conv_lhs => rw [CartanStableSubmodule.eq_iSup_inf_rootSpace H S hHS]
  refine iSup_le fun α => ?_
  by_cases hα : α.IsZero
  · have hz : rootSpace H α = H.toLieSubmodule := by
      simpa only [hα.eq] using (rootSpace_zero_eq K L H)
    rw [hz]
    exact inf_le_right.trans le_sup_left
  · by_cases h : rootSpace H α ≤ N
    · exact inf_le_right.trans
        (le_sup_of_le_right (le_iSup₂_of_le
          (⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩⟩ : H.root)
          h le_rfl))
    · have ha := Submodule.isAtom_iff_finrank_eq_one.mpr
        (LieAlgebra.IsKilling.finrank_rootSpace_eq_one α hα)
      have hz : N ⊓ rootSpace H (α : H → K) = ⊥ :=
        LieSubmodule.toSubmodule_injective
          ((ha.not_le_iff_disjoint.mp h).symm.eq_bot)
      exact hz.le.trans bot_le

/-- The root support of a solvable subalgebra containing `H` is one-sided. -/
theorem solvableCartanSubalgebra_no_opposite
    [LieAlgebra.IsSolvable S] (α : Weight K H L) (hα : α.IsNonZero)
    (hpos : rootSpace H α ≤ cartanStableSubmodule H S hHS)
    (hneg : rootSpace H (-α) ≤ cartanStableSubmodule H S hHS) : False := by
  apply SolvableSubalgebra.not_contains_opposite_rootSpaces H S α hα
  · intro x hx
    exact mem_cartanStableSubmodule H S hHS x |>.mp (hpos hx)
  · intro x hx
    exact mem_cartanStableSubmodule H S hHS x |>.mp (hneg hx)

/-- The nonzero roots whose whole generalized root spaces lie in `S`. -/
def cartanRootSupport : Set (Weight K H L) :=
  {α | α.IsNonZero ∧ rootSpace H α ≤ cartanStableSubmodule H S hHS}

/-- For these parameters,

```lean
False
```
-/
theorem cartanRootSupport_no_opposite [LieAlgebra.IsSolvable S]
    (α : Weight K H L) (hα : α ∈ cartanRootSupport H S hHS)
    (hneg : -α ∈ cartanRootSupport H S hHS) : False := by
  exact solvableCartanSubalgebra_no_opposite H S hHS α hα.1 hα.2 hneg.2

/-- For these parameters,

```lean
γ ∈ cartanRootSupport H S hHS
```
-/
theorem cartanRootSupport_add
    (α β γ : Weight K H L)
    (hα : α ∈ cartanRootSupport H S hHS)
    (hβ : β ∈ cartanRootSupport H S hHS)
    (hγ : γ.IsNonZero) (hsum : (γ : H → K) = α + β) :
    γ ∈ cartanRootSupport H S hHS := by
  refine ⟨hγ, ?_⟩
  intro z hz
  apply (mem_cartanStableSubmodule H S hHS z).mpr
  apply subalgebra_contains_rootSpace_of_sum S α β γ hα.1 hβ.1 hγ hsum
  · intro x hx
    exact (mem_cartanStableSubmodule H S hHS x).mp (hα.2 hx)
  · intro x hx
    exact (mem_cartanStableSubmodule H S hHS x).mp (hβ.2 hx)
  · exact hz

/-- Once a base orients every root occurring in `S` positively, the whole
Cartan-stable subalgebra lies in the associated positive root-space sum. -/
theorem CartanStableSubmodule.le_positiveRootHull
    (b : (rootSystem H).Base)
    (hpositive : ∀ α : H.root,
      rootSpace H α.val ≤ cartanStableSubmodule H S hHS → b.IsPos α) :
    cartanStableSubmodule H S hHS ≤ H.toLieSubmodule ⊔
      ⨆ (α : H.root) (_ : b.IsPos α), rootSpace H α.val := by
  rw [CartanStableSubmodule.eq_cartan_sup_contained_roots H S hHS]
  refine sup_le_sup le_rfl (iSup₂_le fun α hα => ?_)
  exact le_iSup₂_of_le α (hpositive α hα) le_rfl

end ReductiveGroups
