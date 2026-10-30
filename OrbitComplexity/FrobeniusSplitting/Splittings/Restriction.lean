import OrbitComplexity.FrobeniusSplitting.Splittings.Scheme
import Mathlib.Algebra.CharP.Algebra

/-! # Restriction of splittings to open subschemes -/

namespace FrobeniusSplitting

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace SchemeSplitting

/-- A splitting restricts to every open subscheme. -/
def restrict {X : Scheme} {q : ℕ} (splitting : SchemeSplitting X q) (U : X.Opens) :
    SchemeSplitting U.toScheme q where
  onOpen V := splitting.onOpen (U.ι ''ᵁ V)
  restrict_comm h s := splitting.restrict_comm (Set.image_mono h) s

end SchemeSplitting

/-- Nonempty open subsets of a scheme over a field have the characteristic of the field. -/
theorem charP_sections {K : Type u} [Field K] {q : ℕ} [CharP K q]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (U : X.Opens) [Nonempty U] :
    CharP Γ(X, U) q := by
  let f : CommRingCat.of K ⟶ Γ(X, U) :=
    (Scheme.ΓSpecIso (.of K)).inv ≫ (U.ι ≫ base).appTop ≫ U.topIso.hom
  exact charP_of_injective_ringHom f.hom.injective q

end FrobeniusSplitting
