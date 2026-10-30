import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRoots

/-!
# Root-character values fixed by a Weyl representative

A commuting torus point acts by the same scalar on a root weight space and
its Weyl translate. Nonzero root vectors detect the equality of the character values.
-/

noncomputable section
namespace ReductiveGroups.ReductiveGroupData
open TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- A Weyl representative commuting with a torus point preserves its root-character values. -/
theorem rootCharacter_eq_of_weyl_comm (w : G.weylGroup)
    (z : WithConv (MonoidAlgebra K G.characters →ₐ[K] K))
    (hcomm : G.weylPoint w * AlgHom.mapDomain G.torusSplit z =
      AlgHom.mapDomain G.torusSplit z * G.weylPoint w) (r : G.rootIndex) :
    z.ofConv (MonoidAlgebra.single (G.rootCharacter (G.rootSystem.weylGroupToPerm w r)) 1) =
      z.ofConv (MonoidAlgebra.single (G.rootCharacter r) 1) := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (G.rootWeightSpace_ne_bot r)
  have hy : affineGroupAdjointRepresentation (G.weylPoint w) x ∈
      G.rootWeightSpace (G.rootSystem.weylGroupToPerm w r) := by
    rw [← G.weylPoint_rootWeightSpace w r]
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hy0 : affineGroupAdjointRepresentation (G.weylPoint w) x ≠ 0 := by
    intro hzero
    apply hx0
    apply (affineGroupAdjointLieEquiv (G.weylPoint w)).injective
    exact hzero.trans (map_zero _).symm
  have ha : affineGroupAdjointRepresentation (AlgHom.mapDomain G.torusSplit z)
      (affineGroupAdjointRepresentation (G.weylPoint w) x) =
      affineGroupAdjointRepresentation (G.weylPoint w)
        (affineGroupAdjointRepresentation (AlgHom.mapDomain G.torusSplit z) x) := by
    rw [← Module.End.mul_apply, ← map_mul, ← hcomm, map_mul, Module.End.mul_apply]
  rw [AffineGroupAdjoint.eq_character_of_mem_weight G.torusSplit
      (G.rootCharacter (G.rootSystem.weylGroupToPerm w r)) z _ hy,
    AffineGroupAdjoint.eq_character_of_mem_weight G.torusSplit
      (G.rootCharacter r) z x hx, map_smul] at ha
  exact smul_left_injective K hy0 ha

end ReductiveGroups.ReductiveGroupData
