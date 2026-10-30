import OrbitComplexity.SchubertGeometry.FlagVariety.BigCellPoints
import OrbitComplexity.GroupActions.Varieties.OpenPoints
import OrbitComplexity.GroupActions.Varieties.IrreduciblePoints
import Mathlib.Topology.Algebra.Group.Basic

/-! # Generation by the opposite unipotent subgroup and Borel

A subgroup containing the nonempty open big cell is all of the irreducible group.
-/

open AlgebraicGeometry Topology

namespace SchubertGeometry
noncomputable section
universe u

private theorem subgroup_eq_top_of_open {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [PreirreducibleSpace Γ] (H : Subgroup Γ)
    (U : Set Γ) (hU : IsOpen U) (hne : U.Nonempty) (hUH : U ⊆ H) : H = ⊤ := by
  apply (Subgroup.eq_top_iff' H).mpr
  intro a
  have ht : IsOpen ((Homeomorph.mulLeft a) '' U) :=
    (Homeomorph.mulLeft a).isOpenMap U hU
  obtain ⟨z, hzU, hz⟩ := nonempty_preirreducible_inter hU ht hne
    (hne.image (Homeomorph.mulLeft a))
  obtain ⟨v, hv, rfl⟩ := hz
  have hprod : a * v ∈ H := hUH hzU
  have he : a = (a * v) * v⁻¹ := by group
  rw [he]
  exact H.mul_mem hprod (H.inv_mem (hUH hv))

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The opposite unipotent subgroup and Borel subgroup generate all group points. -/
theorem oppositeUnipotent_borel_generate :
    G.oppositeUnipotentPoints ⊔ G.borelPoints = ⊤ := by
  have : IrreducibleSpace G.points :=
    (GroupActions.reductivePointsHomeomorph G).irreducibleSpace_iff.mpr inferInstance
  let H : Subgroup G.points := G.oppositeUnipotentPoints ⊔ G.borelPoints
  let U : Set G.points := (GroupActions.reductivePointsHomeomorph G) ⁻¹'
    Set.range (GroupActions.Variety.mapPoints (bigCellMorphism G))
  have hU : IsOpen U :=
    (GroupActions.Variety.isOpenEmbedding_mapPoints (bigCellMorphism G)).isOpen_range.preimage
      (GroupActions.reductivePointsHomeomorph G).continuous
  have hne : U.Nonempty := by
    let x := (bigCellPointsEquiv G).symm (1, 1)
    refine ⟨(GroupActions.reductivePointsEquiv G).symm
      (GroupActions.Variety.mapPoints (bigCellMorphism G) x), ?_⟩
    change (GroupActions.reductivePointsEquiv G)
      ((GroupActions.reductivePointsEquiv G).symm _) ∈
        Set.range (GroupActions.Variety.mapPoints (bigCellMorphism G))
    rw [Equiv.apply_symm_apply]
    exact ⟨x, rfl⟩
  apply subgroup_eq_top_of_open H U hU hne
  intro g hg
  obtain ⟨x, hx⟩ := hg
  have he :
      (GroupActions.oppositeUnipotentPointsMulEquiv G (bigCellPointsEquiv G x).1 : G.points) *
        (GroupActions.borelPointsMulEquiv G (bigCellPointsEquiv G x).2 : G.points) = g :=
    (GroupActions.reductivePointsEquiv G).injective
      ((bigCellMorphism_points G x).symm.trans hx)
  rw [← he]
  exact H.mul_mem ((show G.oppositeUnipotentPoints ≤ H from le_sup_left)
    (GroupActions.oppositeUnipotentPointsMulEquiv G
    (bigCellPointsEquiv G x).1).property)
      ((show G.borelPoints ≤ H from le_sup_right)
        (GroupActions.borelPointsMulEquiv G (bigCellPointsEquiv G x).2).property)

end
end SchubertGeometry