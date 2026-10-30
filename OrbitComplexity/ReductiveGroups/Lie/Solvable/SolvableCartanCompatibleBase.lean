import OrbitComplexity.ReductiveGroups.Lie.Solvable.SolvableCartanRootDecomposition
import OrbitComplexity.ReductiveGroups.Roots.Inversions.ClosedRootSumSeparator
import OrbitComplexity.ReductiveGroups.Roots.Inversions.BasePositiveClosure

/-!
# Solvable Cartan Compatible Base

The root support of a solvable Cartan-containing subalgebra
selects a compatible base. -/

noncomputable section
namespace ReductiveGroups

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (H S : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  [LieAlgebra.IsSolvable S] (hHS : H ≤ S)

/-- The solvable root support is positive for some base of the
Cartan root system. -/
theorem SolvableCartanCompatibleBase.exists_base_for_solvable_cartan_support :
    ∃ b : (rootSystem H).Base,
      ∀ α : H.root,
        rootSpace H α.val ≤ cartanStableSubmodule H S hHS → b.IsPos α := by
  let s : Set H.root := {α | (α : Weight K H L) ∈ cartanRootSupport H S hHS}
  have hopp : ∀ α ∈ s, ∀ β ∈ s,
      (rootSystem H).root α ≠ -(rootSystem H).root β := by
    intro α hα β hβ heq
    have hroot : (α : Weight K H L) = -(β : Weight K H L) := by
      apply Weight.ext
      intro z
      have h := LinearMap.congr_fun heq z
      simpa [Weight.toLinear_apply, Weight.coe_neg] using h
    have hβeq : (β : Weight K H L) = -(α : Weight K H L) := by
      rw [hroot]
      simp
    have hneg : -(α : Weight K H L) ∈ cartanRootSupport H S hHS := by
      rw [← hβeq]
      exact hβ
    exact cartanRootSupport_no_opposite H S hHS _ hα hneg
  have hclosed : ∀ α ∈ s, ∀ β ∈ s, ∀ γ,
      (rootSystem H).root γ = (rootSystem H).root α + (rootSystem H).root β →
      γ ∈ s := by
    intro α hα β hβ γ hsum
    have hsumW : ((γ : Weight K H L) : H → K) =
        (α : H → K) + (β : H → K) := by
      funext z
      have h := LinearMap.congr_fun hsum z
      simpa [Weight.toLinear_apply] using h
    exact cartanRootSupport_add H S hHS _ _ _ hα hβ
      ((Finset.mem_filter.mp γ.property).2)
      hsumW
  have hbase := exists_base_containing_closed_asymmetric (rootSystem H) s
  obtain ⟨b, hb⟩ := hbase hopp hclosed
  refine ⟨b, ?_⟩
  intro α hα
  have hsα : α ∈ s := ⟨(Finset.mem_filter.mp α.property).2, hα⟩
  exact isPos_of_mem_simple_root_closure (rootSystem H) b α (hb α hsα)

/-- A solvable subalgebra containing the Cartan lies in the positive
root-space hull for a base selected by its own root support. -/
theorem SolvableCartanCompatibleBase.exists_hull_containing_solvable_cartan :
    ∃ b : (rootSystem H).Base,
      cartanStableSubmodule H S hHS ≤ H.toLieSubmodule ⊔
        ⨆ (α : H.root) (_ : b.IsPos α), rootSpace H α.val := by
  obtain ⟨b, hb⟩ := SolvableCartanCompatibleBase.exists_base_for_solvable_cartan_support H S hHS
  exact ⟨b, CartanStableSubmodule.le_positiveRootHull H S hHS b hb⟩

end ReductiveGroups
