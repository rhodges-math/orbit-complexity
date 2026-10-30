import OrbitComplexity.SchubertGeometry.Roots.Subgroups

/-! # Weyl conjugation of the canonical root subgroups -/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- Weyl-point conjugation carries a canonical root subgroup to its transported root. -/
theorem rootSubgroup_weyl_conjugate (w : G.weylGroup) (r : G.rootIndex) :
    (rootSubgroupPoints G r).map (MulAut.conj (G.weylPoint w)).toMonoidHom =
      rootSubgroupPoints G (G.rootSystem.weylGroupToPerm w r) := by
  let x := (rootParameterMap G r).comp (affineGroupConjugationBialgHom (G.weylPoint w))
  have hx : gaAffineGroupTangent x ∈
      G.rootWeightSpace (G.rootSystem.weylGroupToPerm w r) := by
    rw [show x = _ from rfl, gaTangent_comp_conjugation]
    have h : affineGroupAdjointLieEquiv (G.weylPoint w)
        (gaAffineGroupTangent (rootParameterMap G r)) ∈
        (G.rootWeightSpace r).map
          ((affineGroupAdjointLieEquiv (G.weylPoint w)).toLinearEquiv :
            G.tangent →ₗ[K] G.tangent) :=
      Submodule.mem_map.mpr ⟨_, rootParameterMap_tangent_mem G r, rfl⟩
    rw [G.weylPoint_rootWeightSpace] at h
    exact h
  have hx0 : gaAffineGroupTangent x ≠ 0 := by
    rw [show x = _ from rfl, gaTangent_comp_conjugation]
    let e : G.tangent ≃ₗ[K] G.tangent :=
      (affineGroupAdjointLieEquiv (G.weylPoint w)).toLinearEquiv
    intro h
    exact rootParameterMap_tangent_ne_zero G r (e.injective (h.trans (map_zero e).symm))
  apply SetLike.coe_injective
  rw [← rootSubgroupPoints_eq_range G _ x hx hx0]
  ext g
  constructor
  · rintro ⟨q, ⟨a, rfl⟩, rfl⟩
    exact ⟨a.toAdd, gaPoints_comp_conjugation (rootParameterMap G r) (G.weylPoint w) a⟩
  · rintro ⟨a, rfl⟩
    exact ⟨gaParameterPoint (rootParameterMap G r) a, ⟨Multiplicative.ofAdd a, rfl⟩,
      (gaPoints_comp_conjugation (rootParameterMap G r) (G.weylPoint w)
        (Multiplicative.ofAdd a)).symm⟩

end
end SchubertGeometry
