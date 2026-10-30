import OrbitComplexity.GroupActions.Rosenlicht.BirationalEquivariance
import OrbitComplexity.GroupActions.Rosenlicht.OpenComplexity

/-!
# Birational invariance of complexity

An equivariant birational rational map identifies invariant function fields.
The transcendence-degree formula then identifies minimum orbit codimensions.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (H X Y : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
variable [IrreducibleSpace X.scheme] [IrreducibleSpace Y.scheme]

/-- An equivariant birational rational map identifies invariant function fields
by pullback, without requiring stable source or target domains. -/
def invariantFieldBirationalEquiv (f : X.scheme.PartialIso Y.scheme)
    (hf : f.IsOver X.toSpec Y.toSpec)
    (heq : RationalEquivariant (schemeTranslationHom H X) (schemeTranslationHom H Y)
      f.toPartialMap) :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : Y.scheme.Over (Spec (.of K)) := ⟨Y.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : IsIntegral Y.scheme := isIntegral_of_irreducibleSpace_of_isReduced Y.scheme
    invariantField H Y ≃ₐ[K] invariantField H X := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  let _ : Y.scheme.Over (Spec (.of K)) := ⟨Y.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral Y.scheme := isIntegral_of_irreducibleSpace_of_isReduced Y.scheme
  let _ := functionFieldAction (schemeTranslationHom H X)
  let _ := functionFieldAction (schemeTranslationHom H Y)
  have : SMulCommClass H.points K X.scheme.functionField :=
    functionFieldAction_smulComm K (translationHom H X)
  have : SMulCommClass H.points K Y.scheme.functionField :=
    functionFieldAction_smulComm K (translationHom H Y)
  apply fixedFieldEquiv (partialIsoPullbackAlgEquiv K f hf)
  intro h a
  exact partialIsoPullback_equivariant (schemeTranslationHom H X)
    (schemeTranslationHom H Y) f heq h a

/-- Equivariantly birational irreducible varieties have equal minimum orbit
codimension for an irreducible algebraic group. -/
theorem minOrbitCodim_eq_of_birational [IsAlgClosed K] [IrreducibleSpace H.scheme]
    (f : X.scheme.PartialIso Y.scheme) (hf : f.IsOver X.toSpec Y.toSpec)
    (heq : RationalEquivariant (schemeTranslationHom H X) (schemeTranslationHom H Y)
      f.toPartialMap) : minOrbitCodim H X = minOrbitCodim H Y := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  let _ : Y.scheme.Over (Spec (.of K)) := ⟨Y.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have : IsIntegral Y.scheme := isIntegral_of_irreducibleSpace_of_isReduced Y.scheme
  rw [minOrbitCodim_eq_trdeg H X, minOrbitCodim_eq_trdeg H Y]
  simpa only [Cardinal.toNat_lift] using congrArg Cardinal.toNat
    (invariantFieldBirationalEquiv H X Y f hf heq).symm.lift_trdeg_eq

end

end GroupActions.Variety
