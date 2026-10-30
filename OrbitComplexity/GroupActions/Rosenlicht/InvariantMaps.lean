import OrbitComplexity.GroupActions.Rosenlicht.FieldModels
import OrbitComplexity.GroupActions.Rosenlicht.FiniteInvariants
import OrbitComplexity.GroupActions.Rosenlicht.RationalDominance
import OrbitComplexity.GroupActions.Varieties.FunctionFieldDimension
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Rational maps associated to intermediate fields

A finitely generated intermediate field of a variety's function field has an
affine variety model. The field inclusion spreads to a rational map into that
model. Applying this construction to invariant functions gives the rational map
associated to an algebraic group action.

## Main definitions

* `intermediateRationalMap`: the rational map associated to an intermediate field.
* `Variety.invariantModel`: an affine model of the field of invariant functions.
* `Variety.invariantMap`: the rational map to that affine model.

## Main results

* `intermediateRationalMap_field`: the generic restriction is the field inclusion.
* `intermediateRationalMap_dominant`: intermediate-field inclusions give dominant maps.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable (K : Type u) [Field K]
variable {X : Scheme.{u}} [X.Over (Spec (.of K))] [IsIntegral X]
variable (E : IntermediateField K X.functionField) [Algebra.EssFiniteType K E]

private def modelInclusion : fieldModelAlgebra K E →ₐ[K] X.functionField :=
  E.val.comp (fieldModelAlgebra K E).val

private lemma modelInclusion_over :
    Spec.map (CommRingCat.ofHom (modelInclusion K E).toRingHom) ≫
        (fieldModel K E).toSpec =
      X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (.of K)) := by
  rw [Scheme.fromSpecStalk_comp_over]
  change Spec.map (CommRingCat.ofHom (modelInclusion K E).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (fieldModelAlgebra K E))) =
      Spec.map (CommRingCat.ofHom (algebraMap K X.functionField))
  rw [← Spec.map_comp]
  congr 1

/-- A finitely generated intermediate field gives a rational map into its affine model. -/
def intermediateRationalMap : X ⤏ (fieldModel K E).scheme :=
  Scheme.RationalMap.ofFunctionField (X ↘ Spec (.of K)) (fieldModel K E).toSpec
    (Spec.map (CommRingCat.ofHom (modelInclusion K E).toRingHom)) (modelInclusion_over K E)

/-- The generic restriction of the rational map is induced by the field inclusion. -/
theorem intermediateRationalMap_field :
    (intermediateRationalMap K E).fromFunctionField =
      Spec.map (CommRingCat.ofHom (E.val.comp (fieldModelAlgebra K E).val).toRingHom) :=
  Scheme.RationalMap.fromFunctionField_ofFunctionField (X ↘ Spec (.of K))
    (fieldModel K E).toSpec _ (modelInclusion_over K E)

/-- The rational map associated to an intermediate field is dominant. -/
instance intermediateRationalMap_dominant : (intermediateRationalMap K E).IsDominant := by
  have hi : Function.Injective (modelInclusion K E) :=
    E.val.injective.comp Subtype.val_injective
  have : IsDominant (intermediateRationalMap K E).fromFunctionField := by
    rw [intermediateRationalMap_field]
    constructor
    change DenseRange (PrimeSpectrum.comap (modelInclusion K E).toRingHom)
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot (modelInclusion K E).toRingHom).mp hi]
    exact bot_le
  exact rationalMap_dominant_of_generic _

namespace Variety

variable {K} (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- An affine variety whose function field is the field of invariant rational functions. -/
def invariantModel : GroupActions.Variety K := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  exact fieldModel K (invariantField H X)

/-- The affine model of the invariant field is integral. -/
instance invariantModel_integral : IsIntegral (invariantModel H X).scheme := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  exact fieldModel_integral K (invariantField H X)

/-- The function field of the invariant-field model is the invariant field,
compatibly with the base field. -/
def invariantModelFieldEquiv :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : (invariantModel H X).scheme.Over (Spec (.of K)) :=
      ⟨(invariantModel H X).toSpec⟩
    (invariantModel H X).scheme.functionField ≃ₐ[K] invariantField H X := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ : (invariantModel H X).scheme.Over (Spec (.of K)) :=
    ⟨(invariantModel H X).toSpec⟩
  have := invariantField_essFiniteType H X
  exact fieldModelFieldEquiv K (invariantField H X)

/-- The dimension of the invariant-field model is the transcendence degree
of invariant rational functions. -/
theorem invariantModel_natDim :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    (invariantModel H X).natDim = (Algebra.trdeg K (invariantField H X)).toNat := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  let _ : (invariantModel H X).scheme.Over (Spec (.of K)) :=
    ⟨(invariantModel H X).toSpec⟩
  apply (invariantModel H X).natDim_functionField.trans
  simpa only [Cardinal.toNat_lift] using congrArg Cardinal.toNat
    (invariantModelFieldEquiv H X).lift_trdeg_eq

/-- The rational map associated to the field inclusion of invariant rational functions. -/
def invariantMap : X.scheme ⤏ (invariantModel H X).scheme := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  exact intermediateRationalMap K (invariantField H X)

/-- The rational map associated to invariant functions is dominant. -/
instance invariantMap_dominant : (invariantMap H X).IsDominant := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  exact intermediateRationalMap_dominant K (invariantField H X)

end Variety

end

end GroupActions
