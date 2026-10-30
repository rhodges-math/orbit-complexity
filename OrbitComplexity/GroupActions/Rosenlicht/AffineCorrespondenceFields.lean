import OrbitComplexity.GroupActions.Rosenlicht.TensorFieldGenerators
import OrbitComplexity.GroupActions.Rosenlicht.FieldCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Coordinate fields of affine closed correspondences

A closed subscheme of the spectrum of a tensor product has a coordinate ring
which is a quotient of that tensor product. For an integral closed subscheme,
the two factor images consequently generate its function field.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u

variable {K A B : Type u} [Field K]
variable [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
variable {Z : Scheme.{u}}

/-- The coordinate homomorphism of a morphism into the spectrum of a tensor product. -/
def tensorCoordinateMap (i : Z ⟶ Spec (.of (A ⊗[K] B))) :
    A ⊗[K] B →+* Γ(Z, ⊤) :=
  ((Scheme.ΓSpecIso (.of (A ⊗[K] B))).inv ≫ i.appTop).hom

/-- A closed immersion into a tensor-product spectrum is surjective on coordinates. -/
theorem tensorCoordinateMap_surjective (i : Z ⟶ Spec (.of (A ⊗[K] B)))
    [IsClosedImmersion i] : Function.Surjective (tensorCoordinateMap i) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).2.comp
    (Scheme.ΓSpecIso (.of (A ⊗[K] B))).commRingCatIsoToRingEquiv.symm.surjective

/-- The left tensor coordinate is pulled back from the first affine spectrum. -/
theorem tensorCoordinateMap_left (i : Z ⟶ Spec (.of (A ⊗[K] B))) (a : A) :
    tensorCoordinateMap i (a ⊗ₜ[K] 1) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫
        (i ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom)).appTop) a := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The right tensor coordinate is pulled back from the second affine spectrum. -/
theorem tensorCoordinateMap_right (i : Z ⟶ Spec (.of (A ⊗[K] B))) (b : B) :
    tensorCoordinateMap i (1 ⊗ₜ[K] b) =
      ((Scheme.ΓSpecIso (.of B)).inv ≫
        (i ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom)).appTop) b := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The two coordinate factors generate the function field of an integral
closed subscheme of a tensor-product spectrum. -/
theorem closedTensorField_adjoin [IsIntegral Z] [Algebra K Z.functionField]
    (i : Z ⟶ Spec (.of (A ⊗[K] B))) [IsClosedImmersion i] :
    IntermediateField.adjoin K
      (Set.range (fun a : A ↦ Z.germToFunctionField ⊤
        (tensorCoordinateMap i (a ⊗ₜ[K] 1))) ∪
      Set.range (fun b : B ↦ Z.germToFunctionField ⊤
        (tensorCoordinateMap i (1 ⊗ₜ[K] b)))) = ⊤ := by
  have : IsAffine Z := isAffine_of_isAffineHom i
  have : IsFractionRing Γ(Z, ⊤) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z ⊤ (isAffineOpen_top Z)
  exact adjoin_tensorFactors_eq_top K A B Γ(Z, ⊤) Z.functionField
    (tensorCoordinateMap i) (tensorCoordinateMap_surjective i)

/-- Pullbacks of the two affine coordinate rings generate the function field
of an integral closed correspondence with dominant projections. -/
theorem closedTensorField_adjoin_maps [IsIntegral Z] [Algebra K Z.functionField]
    [IsDomain A] [IsDomain B] (i : Z ⟶ Spec (.of (A ⊗[K] B))) [IsClosedImmersion i]
    [IsDominant (i ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom))]
    [IsDominant (i ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom))] :
    IntermediateField.adjoin K
      (Set.range (fun a : A ↦ functionFieldMap (i ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom))
          ((Spec (.of A)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of A)).inv a))) ∪
       Set.range (fun b : B ↦ functionFieldMap (i ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom))
          ((Spec (.of B)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of B)).inv b)))) = ⊤ := by
  have hl (a : A) : Z.germToFunctionField ⊤ (tensorCoordinateMap i (a ⊗ₜ[K] 1)) =
      functionFieldMap (i ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom))
          ((Spec (.of A)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of A)).inv a)) := by
    rw [functionFieldMap_appTop, tensorCoordinateMap_left]
    rfl
  have hr (b : B) : Z.germToFunctionField ⊤ (tensorCoordinateMap i (1 ⊗ₜ[K] b)) =
      functionFieldMap (i ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom))
          ((Spec (.of B)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of B)).inv b)) := by
    rw [functionFieldMap_appTop, tensorCoordinateMap_right]
    rfl
  simpa only [hl, hr] using closedTensorField_adjoin (K := K) i

end

end GroupActions
