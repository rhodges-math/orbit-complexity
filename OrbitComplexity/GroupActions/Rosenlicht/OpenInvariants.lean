import OrbitComplexity.GroupActions.Rosenlicht.GenericOrbit
import OrbitComplexity.GroupActions.Rosenlicht.BirationalFields

/-!
# Invariant fields of equivariant open immersions

An equivariant dominant open immersion induces an equivariant isomorphism of
function fields. Restricting this isomorphism to fixed elements identifies the
invariant fields.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (H X Y : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
variable [IrreducibleSpace X.scheme] [IrreducibleSpace Y.scheme]

omit [IrreducibleSpace X.scheme] [IrreducibleSpace Y.scheme] in
private lemma translate_natural (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f]
    (h : H.points) : translateMorphism H X h ≫ f = f ≫ translateMorphism H Y h := by
  simp only [translateMorphism, IsModHom.map_smul, ModObj.comp_smul,
    Category.comp_id, Category.id_comp, comp_toUnit_assoc]

/-- An equivariant dominant open immersion identifies the fields of invariant
rational functions by pullback. -/
def invariantFieldOpenEquiv (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f]
    [IsOpenImmersion f.left] [IsDominant f.left] :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : Y.scheme.Over (Spec (.of K)) := ⟨Y.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : IsIntegral Y.scheme := isIntegral_of_irreducibleSpace_of_isReduced Y.scheme
    invariantField H Y ≃ₐ[K] invariantField H X := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  let _ : Y.scheme.Over (Spec (.of K)) := ⟨Y.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral Y.scheme := isIntegral_of_irreducibleSpace_of_isReduced Y.scheme
  have : f.left.IsOver (Spec (.of K)) := ⟨f.w⟩
  let _ := functionFieldAction (schemeTranslationHom H X)
  let _ := functionFieldAction (schemeTranslationHom H Y)
  have : SMulCommClass H.points K X.scheme.functionField :=
    functionFieldAction_smulComm K (translationHom H X)
  have : SMulCommClass H.points K Y.scheme.functionField :=
    functionFieldAction_smulComm K (translationHom H Y)
  let e := openFunctionFieldAlgEquiv K (X := X.scheme) (Y := Y.scheme) f.left
  apply fixedFieldEquiv e
  intro h a
  apply functionFieldMap_equivariant (schemeTranslationHom H X)
    (schemeTranslationHom H Y) (f.left : X.scheme ⟶ Y.scheme)
  intro g
  exact congrArg Over.Hom.left (translate_natural H X Y f g)

end

end GroupActions.Variety
