import OrbitComplexity.GroupActions.Rosenlicht.CorrespondenceFields
import OrbitComplexity.GroupActions.Rosenlicht.RelationProjections
import OrbitComplexity.GroupActions.Rosenlicht.FieldGenerators
import OrbitComplexity.GroupActions.Rosenlicht.ActionRelations

/-!
# Function fields of orbit relations

The two projections of an orbit relation closure generate its function field.
A field-generating tuple in the second projection therefore generates it over
the first projection's function field.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- Function-field pullback along the first orbit relation projection. -/
def relationFirstFieldMap :
    X.scheme.functionField →+* (orbitRelationVariety H X).scheme.functionField :=
  functionFieldMap ((orbitRelationProjection H X).left :
    (orbitRelationVariety H X).scheme ⟶ X.scheme)

/-- Function-field pullback along the second orbit relation projection. -/
def relationSecondFieldMap :
    X.scheme.functionField →+* (orbitRelationVariety H X).scheme.functionField :=
  functionFieldMap ((orbitRelationSecond H X).left :
    (orbitRelationVariety H X).scheme ⟶ X.scheme)

private abbrev relationScalarAlgebra :
    Algebra X.scheme.functionField (orbitRelationVariety H X).scheme.functionField :=
  (relationFirstFieldMap H X).toAlgebra

/-- The two projections of the orbit relation closure generate its function field. -/
theorem orbitRelationField_adjoin :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : (orbitRelationVariety H X).scheme.Over (Spec (.of K)) :=
      ⟨(orbitRelationVariety H X).toSpec⟩
    letI : IsIntegral (orbitRelationVariety H X).scheme :=
      isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
    IntermediateField.adjoin K
      (Set.range (relationFirstFieldMap H X) ∪
        Set.range (relationSecondFieldMap H X)) = ⊤ := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ : (orbitRelationVariety H X).scheme.Over (Spec (.of K)) :=
    ⟨(orbitRelationVariety H X).toSpec⟩
  have : IsIntegral (orbitRelationVariety H X).scheme :=
    isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
  have hci : @IsClosedImmersion (orbitRelationVariety H X).scheme
      (pullback X.toSpec X.toSpec) (orbitRelationInclusion H X).left :=
    orbitRelationInclusion_closed H X
  have h₁ : @IsDominant (orbitRelationVariety H X).scheme X.scheme
      ((orbitRelationInclusion H X).left ≫ pullback.fst X.toSpec X.toSpec) :=
    inferInstanceAs (IsDominant (orbitRelationProjection H X).left)
  have h₂ : @IsDominant (orbitRelationVariety H X).scheme X.scheme
      ((orbitRelationInclusion H X).left ≫ pullback.snd X.toSpec X.toSpec) :=
    inferInstanceAs (IsDominant (orbitRelationSecond H X).left)
  exact @closedProductField_adjoin_general K inferInstance X.scheme X.scheme
    inferInstance inferInstance inferInstance inferInstance
    (orbitRelationVariety H X).scheme inferInstance inferInstance
    (orbitRelationInclusion H X).left hci h₁ h₂

/-- A function-field generating tuple pulls back along the second relation
projection to generators over the first projection's function field. -/
theorem orbitRelationField_generators {ι : Type v} (x : ι → X.scheme.functionField) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : (orbitRelationVariety H X).scheme.Over (Spec (.of K)) :=
      ⟨(orbitRelationVariety H X).toSpec⟩
    letI : IsIntegral (orbitRelationVariety H X).scheme :=
      isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
    letI := relationScalarAlgebra H X
    IntermediateField.adjoin K (Set.range x) = ⊤ →
      IntermediateField.adjoin X.scheme.functionField
        (Set.range (fun i ↦ relationSecondFieldMap H X (x i))) = ⊤ := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ : (orbitRelationVariety H X).scheme.Over (Spec (.of K)) :=
    ⟨(orbitRelationVariety H X).toSpec⟩
  have : IsIntegral (orbitRelationVariety H X).scheme :=
    isIntegral_of_irreducibleSpace_of_isReduced (orbitRelationVariety H X).scheme
  let _ := relationScalarAlgebra H X
  let _ : (orbitRelationProjection H X).left.IsOver (Spec (.of K)) :=
    ⟨(orbitRelationProjection H X).w⟩
  let _ : (orbitRelationSecond H X).left.IsOver (Spec (.of K)) :=
    ⟨(orbitRelationSecond H X).w⟩
  have : IsScalarTower K X.scheme.functionField
      (orbitRelationVariety H X).scheme.functionField :=
    IsScalarTower.of_algHom (functionFieldAlgHom K (X := (orbitRelationVariety H X).scheme)
      (Y := X.scheme) (orbitRelationProjection H X).left)
  intro hx
  exact adjoin_twoMaps_generators K X.scheme.functionField
    (orbitRelationVariety H X).scheme.functionField
    (functionFieldAlgHom K (X := (orbitRelationVariety H X).scheme)
      (Y := X.scheme) (orbitRelationSecond H X).left) x hx (orbitRelationField_adjoin H X)

end

end GroupActions.Variety
