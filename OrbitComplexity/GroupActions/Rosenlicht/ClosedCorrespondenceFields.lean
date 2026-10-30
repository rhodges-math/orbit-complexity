import OrbitComplexity.GroupActions.Rosenlicht.AffineCorrespondenceFields
import OrbitComplexity.GroupActions.Rosenlicht.AffineProductCoordinates

/-!
# Function fields of affine closed correspondences

For an integral closed correspondence in a product of affine integral schemes,
with dominant projections, pullback of the two function fields generates the
correspondence's function field.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u

variable (K : Type u) [Field K] (X Y : Scheme.{u})
variable [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] [IsAffine X] [IsAffine Y]
variable [IsIntegral X] [IsIntegral Y]

private abbrev sectionsAlgebra (R : CommRingCat.{u}) (T : Scheme.{u})
    [T.Over (Spec R)] [IsAffine T] : Algebra R Γ(T, ⊤) := inferInstance

private lemma isoSpec_germ (T : Scheme.{u}) [IsIntegral T] [IsAffine T]
    (s : Γ(T, ⊤)) : functionFieldMap T.isoSpec.hom
      ((Spec Γ(T, ⊤)).germToFunctionField ⊤ ((Scheme.ΓSpecIso Γ(T, ⊤)).inv s)) =
        T.germToFunctionField ⊤ s := by
  rw [← affineField_algebraMap Γ(T, ⊤) s]
  exact affineField_isoSpec T s

/-- Dominant projections from an integral closed correspondence in an affine
product generate its function field. -/
theorem closedProductField_adjoin {Z : Scheme.{u}} [IsIntegral Z]
    [Algebra K Z.functionField] (i : Z ⟶ pullback (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))
    [IsClosedImmersion i]
    [IsDominant (i ≫ pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))]
    [IsDominant (i ≫ pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))] :
    IntermediateField.adjoin K
      (Set.range (functionFieldMap
        (i ≫ pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))) ∪
       Set.range (functionFieldMap
        (i ≫ pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))))) = ⊤ := by
  let : Algebra K Γ(X, ⊤) := sectionsAlgebra (.of K) X
  let : Algebra K Γ(Y, ⊤) := sectionsAlgebra (.of K) Y
  let j := i ≫ (affineProductSpecIso (.of K) X Y).hom
  have hj₁ : j ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : Γ(X, ⊤) →ₐ[K]
        Γ(X, ⊤) ⊗[K] Γ(Y, ⊤)).toRingHom) =
      (i ≫ pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))) ≫ X.isoSpec.hom := by
    dsimp only [j]
    erw [Category.assoc, affineProductSpecIso_fst, ← Category.assoc]
  have hj₂ : j ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Γ(Y, ⊤) →ₐ[K]
        Γ(X, ⊤) ⊗[K] Γ(Y, ⊤)).toRingHom) =
      (i ≫ pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K))) ≫ Y.isoSpec.hom := by
    dsimp only [j]
    erw [Category.assoc, affineProductSpecIso_snd, ← Category.assoc]
  have : IsDominant (j ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : Γ(X, ⊤) →ₐ[K]
        Γ(X, ⊤) ⊗[K] Γ(Y, ⊤)).toRingHom)) := by
    rw [hj₁]
    infer_instance
  have : IsDominant (j ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Γ(Y, ⊤) →ₐ[K]
        Γ(X, ⊤) ⊗[K] Γ(Y, ⊤)).toRingHom)) := by
    rw [hj₂]
    infer_instance
  have hl (a : Γ(X, ⊤)) : functionFieldMap (j ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : Γ(X, ⊤) →ₐ[K]
        Γ(X, ⊤) ⊗[K] Γ(Y, ⊤)).toRingHom))
        ((Spec Γ(X, ⊤)).germToFunctionField ⊤ ((Scheme.ΓSpecIso Γ(X, ⊤)).inv a)) =
      functionFieldMap (i ≫ pullback.fst (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))
        (X.germToFunctionField ⊤ a) := by
    rw [functionFieldMap_congr _ _ hj₁, functionFieldMap_comp, RingHom.comp_apply, isoSpec_germ]
  have hr (b : Γ(Y, ⊤)) : functionFieldMap (j ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Γ(Y, ⊤) →ₐ[K]
        Γ(X, ⊤) ⊗[K] Γ(Y, ⊤)).toRingHom))
        ((Spec Γ(Y, ⊤)).germToFunctionField ⊤ ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv b)) =
      functionFieldMap (i ≫ pullback.snd (X ↘ Spec (.of K)) (Y ↘ Spec (.of K)))
        (Y.germToFunctionField ⊤ b) := by
    rw [functionFieldMap_congr _ _ hj₂, functionFieldMap_comp, RingHom.comp_apply, isoSpec_germ]
  have hg := closedTensorField_adjoin_maps (K := K) j
  apply top_le_iff.mp
  rw [← hg]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z (⟨a, rfl⟩ | ⟨b, rfl⟩)
  · exact IntermediateField.subset_adjoin K _
      (Or.inl ⟨X.germToFunctionField ⊤ a, (hl a).symm⟩)
  · exact IntermediateField.subset_adjoin K _
      (Or.inr ⟨Y.germToFunctionField ⊤ b, (hr b).symm⟩)

end

end GroupActions
