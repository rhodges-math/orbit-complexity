import OrbitComplexity.FrobeniusSplitting.Normality.SchemeModels
import OrbitComplexity.GroupActions.Varieties.ProjectiveSpaceBaseChange

/-! # Projective comparisons for the same affine coefficient model -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions FrobeniusSplitting
open scoped TensorProduct
noncomputable section
universe u
namespace SchubertGeometry

private theorem coefficient_base {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    projectiveCoeffMap (ULift.{u} (Fin 2)) f ≫ projectiveToSpec R (ULift.{u} (Fin 2)) =
      projectiveToSpec S (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← projectiveBaseChange_snd (ULift.{u} (Fin 2)) f, Category.assoc,
    ← pullback.condition, ← Category.assoc, projectiveBaseChange_fst]

/-- A affine tensor-model comparison gives the corresponding projective base square. -/
theorem projectiveModel_cartesian {R K A B : Type u}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra K B] (e : K ⊗[R] A ≃ₐ[K] B) :
    IsPullback
      (projectiveCoeffMap (ULift.{u} (Fin 2))
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))
      (projectiveToSpec B (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K B)))
      (projectiveToSpec A (ULift.{u} (Fin 2)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  let : Algebra R B := ((algebraMap K B).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let f : A →+* B := e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  have h : IsPullback (projectiveToSpec B (ULift.{u} (Fin 2)))
      (projectiveCoeffMap (ULift.{u} (Fin 2)) f) (Spec.map (CommRingCat.ofHom f))
      (projectiveToSpec A (ULift.{u} (Fin 2))) :=
    IsPullback.of_iso_pullback ⟨(coefficient_base f).symm⟩
      (projectiveBaseChange (ULift.{u} (Fin 2)) f)
      (projectiveBaseChange_fst _ f) (projectiveBaseChange_snd _ f)
  exact h.flip.paste_vert (isPullback_affineModel e).flip

end SchubertGeometry
