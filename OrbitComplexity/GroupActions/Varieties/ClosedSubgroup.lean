import OrbitComplexity.GroupActions.Varieties.AffineGroup
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-! # Reduced closed subgroup varieties

A reduced Hopf quotient of a reduced finite-type Hopf algebra defines a closed group
subvariety. Its rational points identify with the subgroup cut out by the Hopf ideal.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K]
  (A : TauCeti.FiniteTypeCommHopfAlgCat.{u, u} K) [IsReduced A]
  (I : TauCeti.HopfIdeal K A) [IsReduced (A ⧸ I.toIdeal)]

/-- A reduced quotient Hopf algebra defines an affine closed subgroup variety. -/
def closedSubgroupVariety : Variety K := affineVariety K (A ⧸ I.toIdeal)

/-- The quotient Hopf algebra gives the closed subgroup variety its group structure. -/
instance closedSubgroupVarietyGroup : GrpObj (closedSubgroupVariety A I).toOver := by
  change GrpObj ((Spec (CommRingCat.of (A ⧸ I.toIdeal))).asOver
    (Spec (CommRingCat.of K)))
  infer_instance

/-- The coordinate quotient induces the closed subgroup inclusion. -/
def closedSubgroupInclusion :
    (closedSubgroupVariety A I).toOver ⟶ (affineVariety K A).toOver :=
  (TauCeti.CommHopfAlgCat.quotientSpecι A.obj I).hom.hom

private theorem closedSubgroupInclusion_left :
    (closedSubgroupInclusion A I).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.toIdeal)) := rfl

/-- The coordinate-quotient inclusion is a closed immersion. -/
instance closedSubgroupInclusion_isClosed :
    IsClosedImmersion (closedSubgroupInclusion A I).left :=
  TauCeti.CommHopfAlgCat.isClosedImmersion_quotientSpecι A.obj I

/-- The closed subgroup inclusion preserves multiplication. -/
instance closedSubgroupInclusion_isMonHom : IsMonHom (closedSubgroupInclusion A I) := by
  change IsMonHom (TauCeti.CommHopfAlgCat.quotientSpecι A.obj I).hom.hom
  infer_instance

/-- Rational points of the closed variety identify with the Hopf-ideal point subgroup. -/
def closedSubgroupPointsMulEquiv :
    (closedSubgroupVariety A I).points ≃*
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup A.obj I (CommAlgCat.of K K) :=
  (affineGroupPointsMulEquiv K (A ⧸ I.toIdeal)).symm.trans
    (MonoidHom.ofInjective
      (f := (TauCeti.CommHopfAlgCat.quotientPointsHom A.obj I (CommAlgCat.of K K)).hom)
      (TauCeti.CommHopfAlgCat.quotientPointsHom_injective _ _ _))

omit [IsReduced A] in
private theorem closedSubgroupPoints_coe (x : (closedSubgroupVariety A I).points) :
    (closedSubgroupPointsMulEquiv A I x : WithConv (A →ₐ[K] K)) =
      TauCeti.CommHopfAlgCat.quotientPointsHom A.obj I (CommAlgCat.of K K)
        (WithConv.toConv (affinePointsEquiv.symm x)) := rfl

/-- The closed-subgroup point identification commutes with its inclusion. -/
theorem closedSubgroupInclusion_points (x : (closedSubgroupVariety A I).points) :
    Variety.mapPoints (closedSubgroupInclusion A I) x =
      affineGroupPointsMulEquiv K A (closedSubgroupPointsMulEquiv A I x) := by
  let e : ((A ⧸ I.toIdeal) →ₐ[K] K) ≃ (closedSubgroupVariety A I).points :=
    affinePointsEquiv
  obtain ⟨f, rfl⟩ := e.surjective x
  have hf : (closedSubgroupPointsMulEquiv A I (e f) : WithConv (A →ₐ[K] K)) =
      TauCeti.CommHopfAlgCat.quotientPointsHom A.obj I (CommAlgCat.of K K)
        (WithConv.toConv f) := by
    rw [closedSubgroupPoints_coe]
    change TauCeti.CommHopfAlgCat.quotientPointsHom A.obj I (CommAlgCat.of K K)
      (WithConv.toConv (e.symm (e f))) = _
    rw [e.symm_apply_apply]
  apply Subtype.ext
  change (e f).val ≫ (closedSubgroupInclusion A I).left =
    (affineGroupPointsMulEquiv K A (closedSubgroupPointsMulEquiv A I (e f))).val
  rw [hf, affineGroupPointsMulEquiv_apply, closedSubgroupInclusion_left]
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.toIdeal)) =
    Spec.map (CommRingCat.ofHom (f.comp (Ideal.Quotient.mkₐ K I.toIdeal)).toRingHom)
  rw [← Spec.map_comp]
  rfl

end

end GroupActions
