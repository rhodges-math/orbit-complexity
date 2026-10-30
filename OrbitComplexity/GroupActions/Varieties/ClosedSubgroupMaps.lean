import OrbitComplexity.GroupActions.Varieties.ClosedSubgroup

/-! # Inclusions of reduced closed subgroups

An inclusion of Hopf ideals gives a closed group morphism in the reverse direction.
The morphism commutes with the ambient inclusion and with the rational-point subgroups.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K]
  (A : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K) [IsReduced A]
  (I J : TauCeti.HopfIdeal K A) [IsReduced (A ⧸ I.toIdeal)] [IsReduced (A ⧸ J.toIdeal)]
  (h : I ≤ J)

/-- An inclusion of Hopf ideals induces the reverse inclusion of closed subgroup varieties. -/
def closedSubgroupMap :
    (closedSubgroupVariety A J).toOver ⟶ (closedSubgroupVariety A I).toOver :=
  (TauCeti.CommHopfAlgCat.quotientSpecMapOfLe A.obj h).hom.hom

/-- The morphism induced by an inclusion of Hopf ideals is a closed immersion. -/
instance closedSubgroupMap_isClosed : IsClosedImmersion (closedSubgroupMap A I J h).left :=
  TauCeti.CommHopfAlgCat.isClosedImmersion_quotientSpecMapOfLe A.obj h

/-- The closed subgroup morphism preserves multiplication. -/
instance closedSubgroupMap_isMonHom : IsMonHom (closedSubgroupMap A I J h) := by
  change IsMonHom (TauCeti.CommHopfAlgCat.quotientSpecMapOfLe A.obj h).hom.hom
  infer_instance

/-- Nested closed subgroup inclusions commute with their ambient inclusions. -/
theorem closedSubgroupMap_comp_inclusion :
    closedSubgroupMap A I J h ≫ closedSubgroupInclusion A I = closedSubgroupInclusion A J :=
  congrArg (fun f ↦ f.hom.hom)
    (TauCeti.CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι A.obj h)

/-- The morphism of closed subgroups preserves the corresponding ambient rational point. -/
theorem closedSubgroupMap_points (x : (closedSubgroupVariety A J).points) :
    (closedSubgroupPointsMulEquiv A I (Variety.mapPoints (closedSubgroupMap A I J h) x) :
      WithConv (A →ₐ[K] K)) = (closedSubgroupPointsMulEquiv A J x : WithConv (A →ₐ[K] K)) := by
  have he : Variety.mapPoints (closedSubgroupInclusion A I)
      (Variety.mapPoints (closedSubgroupMap A I J h) x) =
        Variety.mapPoints (closedSubgroupInclusion A J) x := by
    rw [← Variety.mapPoints_comp, closedSubgroupMap_comp_inclusion]
  apply (affineGroupPointsMulEquiv K A).injective
  exact (closedSubgroupInclusion_points A I _).symm.trans
    (he.trans (closedSubgroupInclusion_points A J x))

end

end GroupActions
