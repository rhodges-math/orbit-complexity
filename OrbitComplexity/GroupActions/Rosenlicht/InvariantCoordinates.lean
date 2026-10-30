import OrbitComplexity.GroupActions.Rosenlicht.PartialCoordinates
import OrbitComplexity.GroupActions.Rosenlicht.InvariantDomains

/-!
# Invariant coordinate germs

Coordinate functions pulled back from the invariant-field model have their prescribed
invariant rational germs.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

/-- Pulling a coordinate of the invariant-field model back along the invariant
morphism has that coordinate as its rational germ. -/
theorem invariantCoordinate_germ :
    letI : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    letI : Algebra.EssFiniteType K (invariantField H X) := invariantField_essFiniteType H X
    letI : Nonempty (invariantMap H X).domain :=
      Set.nonempty_coe_sort.mpr (invariantDomain_nonempty H X)
    ∀ a : fieldModelAlgebra K (invariantField H X),
      X.scheme.germToFunctionField (invariantMap H X).domain
        ((invariantMap H X).domain.topIso.hom ((invariantMorphism H X).left.appTop
          ((Scheme.ΓSpecIso (.of (fieldModelAlgebra K (invariantField H X)))).inv a))) =
        a.val.val := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  have : Nonempty (invariantMap H X).domain :=
    Set.nonempty_coe_sort.mpr (invariantDomain_nonempty H X)
  intro a
  let A := fieldModelAlgebra K (invariantField H X)
  let r : X.scheme.PartialMap (Spec (.of A)) := (invariantMap H X).toPartialMap
  let φ : A →+* X.scheme.functionField :=
    ((invariantField H X).val.comp A.val).toRingHom
  have hr : r.fromFunctionField = Spec.map (CommRingCat.ofHom φ) := by
    change (invariantMap H X).toPartialMap.fromFunctionField = _
    rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.toRationalMap_toPartialMap]
    exact intermediateRationalMap_field K (invariantField H X)
  exact partialMap_coordinate_germ X.scheme (.of A) r φ hr a

end

end GroupActions.Variety
