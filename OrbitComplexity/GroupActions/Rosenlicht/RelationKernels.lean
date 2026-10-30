import OrbitComplexity.GroupActions.Rosenlicht.RelationProjections
import OrbitComplexity.GroupActions.Rosenlicht.ActionRelations
import OrbitComplexity.GroupActions.Rosenlicht.FieldCoordinates

/-!
# Polynomial relations in orbit relation fields

Pullback through the dominant relation factor identifies polynomial relations
in the two relation projections with the generic orbit ideal. Injectivity of
function-field pullback preserves the kernel.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory

namespace GroupActions.Variety

noncomputable section

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- Polynomial relations in the two orbit relation projections are exactly
polynomial relations of the generic orbit. -/
theorem relationField_ker_eq {ι : Type v} (x : ι → X.scheme.functionField) :
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : IsIntegral (orbitRelationVariety H X).scheme :=
      isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
    letI : Algebra X.scheme.functionField (orbitRelationVariety H X).scheme.functionField :=
      (functionFieldMap (orbitRelationProjection H X).left).toAlgebra
    RingHom.ker (MvPolynomial.aeval
      (fun i ↦ functionFieldMap (orbitRelationSecond H X).left (x i)) :
        MvPolynomial ι X.scheme.functionField →ₐ[X.scheme.functionField]
          (orbitRelationVariety H X).scheme.functionField) = genericOrbitIdeal H X x := by
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral (orbitRelationVariety H X).scheme :=
    isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
  let _ : Algebra X.scheme.functionField (orbitRelationVariety H X).scheme.functionField :=
    (functionFieldMap (orbitRelationProjection H X).left).toAlgebra
  have : IsIntegral (productVariety H X).scheme := product_integral H X
  have : IsIntegral (productVariety H X).toOver.left := product_integral H X
  have : IsIntegral (H.toOver ⊗ X.toOver).left := product_integral H X
  have hp : (orbitRelationFactor H X).left ≫ (orbitRelationProjection H X).left =
      (snd H.toOver X.toOver).left :=
    congrArg Over.Hom.left (orbitRelationProjection_fac H X)
  have hq : (orbitRelationFactor H X).left ≫ (orbitRelationSecond H X).left =
      (ModObj.smul (M := H.toOver) (X := X.toOver)).left :=
    congrArg Over.Hom.left (orbitRelationSecond_fac H X)
  have : IsDominant (snd H.toOver X.toOver).left := by
    rw [← hp]
    infer_instance
  let c : (orbitRelationVariety H X).scheme.functionField →+*
      (productVariety H X).scheme.functionField :=
    functionFieldMap ((orbitRelationFactor H X).left :
      (productVariety H X).scheme ⟶ (orbitRelationVariety H X).scheme)
  let ev : MvPolynomial ι X.scheme.functionField →ₐ[X.scheme.functionField]
      (orbitRelationVariety H X).scheme.functionField := MvPolynomial.aeval
    (fun i ↦ functionFieldMap (orbitRelationSecond H X).left (x i))
  have hc₁ : c.comp (functionFieldMap (orbitRelationProjection H X).left) =
      functionFieldMap (snd H.toOver X.toOver).left := by
    change (functionFieldMap (orbitRelationFactor H X).left).comp
      (functionFieldMap (orbitRelationProjection H X).left) = _
    rw [← functionFieldMap_comp]
    exact functionFieldMap_congr _ _ hp
  have hc₂ : c.comp (functionFieldMap (orbitRelationSecond H X).left) =
      functionFieldMap (ModObj.smul (M := H.toOver) (X := X.toOver)).left := by
    change (functionFieldMap (orbitRelationFactor H X).left).comp
      (functionFieldMap (orbitRelationSecond H X).left) = _
    rw [← functionFieldMap_comp]
    exact functionFieldMap_congr _ _ hq
  have he : c.comp ev.toRingHom = actionRelationMap H X x := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change c (ev (MvPolynomial.C a)) = actionRelationMap H X x (MvPolynomial.C a)
      simp only [ev, MvPolynomial.aeval_C, actionRelationMap, MvPolynomial.eval₂Hom_C]
      exact DFunLike.congr_fun hc₁ a
    · intro i
      change c (ev (MvPolynomial.X i)) = actionRelationMap H X x (MvPolynomial.X i)
      simp only [ev, MvPolynomial.aeval_X, actionRelationMap, MvPolynomial.eval₂Hom_X']
      exact DFunLike.congr_fun hc₂ (x i)
  rw [← actionRelation_ideal_eq H X x, ← he]
  exact (RingHom.ker_comp_of_injective ev.toRingHom c.injective).symm

end

end GroupActions.Variety
