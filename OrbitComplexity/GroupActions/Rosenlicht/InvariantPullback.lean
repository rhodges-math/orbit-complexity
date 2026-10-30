import OrbitComplexity.GroupActions.Rosenlicht.InvariantCoordinates
import OrbitComplexity.GroupActions.Rosenlicht.ChartGerms
import OrbitComplexity.GroupActions.Rosenlicht.FieldCoordinates

/-!
# Pullback from the invariant-field model

The function-field pullback of the invariant morphism is the prescribed inclusion of
invariant rational functions.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- Pullback by the invariant morphism is the inclusion of the invariant field,
after the canonical identifications of the source and model function fields. -/
theorem invariantMorphism_fieldMap :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : (invariantModel H X).scheme.Over (Spec (.of K)) :=
      ⟨(invariantModel H X).toSpec⟩
    letI : Nonempty (invariantMap H X).domain :=
      Set.nonempty_coe_sort.mpr (invariantDomain_nonempty H X)
    letI : IsDominant (invariantMap H X).domain.ι :=
      Opens.isDominant_ι (invariantMap H X).dense_domain
    functionFieldMap (X := (invariantDomain H X).scheme)
      (Y := (invariantModel H X).scheme) (invariantMorphism H X).left =
      (functionFieldMap (invariantMap H X).domain.ι).comp
        ((invariantField H X).val.toRingHom.comp (invariantModelFieldEquiv H X).toRingHom) := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ : (invariantModel H X).scheme.Over (Spec (.of K)) :=
    ⟨(invariantModel H X).toSpec⟩
  have := invariantField_essFiniteType H X
  let E := invariantField H X
  let A := fieldModelAlgebra K E
  let D := (invariantMap H X).domain
  have : Nonempty D := Set.nonempty_coe_sort.mpr (invariantDomain_nonempty H X)
  have : IsDominant D.ι := Opens.isDominant_ι (invariantMap H X).dense_domain
  have : IsIntegral D.toScheme :=
    isIntegral_of_isOpenImmersion D.ι
  have : Nonempty (⊤ : D.toScheme.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  have : Nonempty (⊤ : (invariantModel H X).scheme.Opens) :=
    ⟨⟨genericPoint (invariantModel H X).scheme, trivial⟩⟩
  let : Algebra A (invariantModel H X).scheme.functionField :=
    inferInstanceAs (Algebra A (Spec (.of A)).functionField)
  have : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  have : IsFractionRing A (invariantModel H X).scheme.functionField :=
    functionField_isFractionRing_of_affine (.of A)
  apply IsLocalization.ringHom_ext (nonZeroDivisors A)
  ext a
  have he : invariantModelFieldEquiv H X
      (algebraMap A (invariantModel H X).scheme.functionField a) = a.val := by
    change (IsLocalization.algEquiv (nonZeroDivisors A)
      (Spec (.of A)).functionField E) (algebraMap A (Spec (.of A)).functionField a) = _
    exact AlgEquiv.commutes _ a
  let f : D.toScheme ⟶ (invariantModel H X).scheme := (invariantMorphism H X).left
  have : IsDominant f := invariantMorphism_dominant H X
  change functionFieldMap f
      (algebraMap A (invariantModel H X).scheme.functionField a) =
    (functionFieldMap D.ι) ((invariantModelFieldEquiv H X
      (algebraMap A (invariantModel H X).scheme.functionField a)).val)
  rw [he]
  have hf := functionFieldMap_appTop f ((Scheme.ΓSpecIso (.of A)).inv a)
  have hg := openFunctionFieldMap_germ D
    (D.topIso.hom (f.appTop ((Scheme.ΓSpecIso (.of A)).inv a)))
  have hv := invariantCoordinate_germ H X a
  change X.scheme.germToFunctionField D
    (D.topIso.hom (f.appTop ((Scheme.ΓSpecIso (.of A)).inv a))) = a.val.val at hv
  rw [hv] at hg
  rw [show D.topIso.inv (D.topIso.hom (f.appTop ((Scheme.ΓSpecIso (.of A)).inv a))) =
      f.appTop ((Scheme.ΓSpecIso (.of A)).inv a) from
      D.topIso.commRingCatIsoToRingEquiv.left_inv _] at hg
  exact hf.trans hg.symm

end

end GroupActions.Variety
