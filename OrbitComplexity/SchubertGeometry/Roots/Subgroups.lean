import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.RootRanges
import OrbitComplexity.SchubertGeometry.Roots.Parameters
import OrbitComplexity.GroupActions.Varieties.AdditiveVariety
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPointInjectivity

/-! # Canonical signed root subgroups

The independently chosen Weyl-conjugate root parameter defines the closed root subgroup.
Any nonzero additive parameter in the same root weight space has exactly its point image.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions TauCeti
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

/-- The root subgroup given by the fixed Weyl-conjugate simple-root parameter. -/
def rootSubgroupPoints (r : G.rootIndex) : Subgroup G.points :=
  (gaAffineGroupPoints (rootParameterMap G r)).range

/-- The fixed root parameter is a closed immersion of the additive group. -/
theorem rootParameterMorphism_isClosed (r : G.rootIndex) :
    IsClosedImmersion (gaMorphism G (rootParameterMap G r)).left := by
  change IsClosedImmersion (Spec.map
    (CommRingCat.ofHom (rootParameterMap G r).toAlgHom.toRingHom))
  exact IsClosedImmersion.spec_of_surjective _
    (gaMorphism_surjective_of_tangent_ne_zero (K := K) (B := G.coordinateAlgebra)
      (rootParameterMap G r) (rootParameterMap_tangent_ne_zero G r))

private theorem parameter_range (r : G.rootIndex) :
    Set.range (fun a : K => gaParameterPoint (rootParameterMap G r) a) =
      (rootSubgroupPoints G r : Set G.points) := by
  ext g
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Multiplicative.ofAdd a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨Multiplicative.toAdd a, ha⟩

/-- Every nonzero additive parameter in a root line has the canonical root-subgroup image. -/
theorem rootSubgroupPoints_eq_range (r : G.rootIndex)
    (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ G.rootWeightSpace r)
    (hx0 : gaAffineGroupTangent x ≠ 0) :
    Set.range (fun a : K => gaParameterPoint x a) =
      (rootSubgroupPoints G r : Set G.points) :=
  (gaParameterPoint_range_of_line (G.rootWeightSpace r) (G.rootWeightSpace_finrank r)
    x (rootParameterMap G r) hx (rootParameterMap_tangent_mem G r)
    hx0 (rootParameterMap_tangent_ne_zero G r)).trans (parameter_range G r)

private theorem punctured_image {A M : Type*} [Zero A] [One M] (f : A → M)
    (hf : Function.Injective f) (hzero : f 0 = 1) :
    f '' {a | a ≠ 0} = Set.range f \ {1} := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, rfl⟩, ?_⟩
    change f a ≠ 1
    exact fun h => ha (hf (h.trans hzero.symm))
  · rintro ⟨⟨a, rfl⟩, ha⟩
    exact ⟨a, fun h => ha (show f a = 1 from (congrArg f h).trans hzero), rfl⟩

/-- Removing zero from a nonzero root parameter removes precisely the subgroup identity. -/
theorem rootSubgroupPoints_eq_puncture (r : G.rootIndex)
    (x : G.coordinateAlgebra →ₐc[K] SymmetricAlgebra K K)
    (hx : gaAffineGroupTangent x ∈ G.rootWeightSpace r)
    (hx0 : gaAffineGroupTangent x ≠ 0) :
    (fun a : K => gaParameterPoint x a) '' {a | a ≠ 0} =
      (rootSubgroupPoints G r : Set G.points) \ {1} := by
  have hi : Function.Injective (fun a : K => gaParameterPoint x a) := by
    intro a b h
    exact congrArg Multiplicative.toAdd
      (GaAffineGroupPoints.injective_of_tangent_ne_zero x hx0 h)
  rw [punctured_image _ hi (gaParameterPoint_zero x),
    rootSubgroupPoints_eq_range G r x hx hx0]

end
end SchubertGeometry
