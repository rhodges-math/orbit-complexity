import Batteries.Tactic.Lint
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Noetherian schemes over finite coefficient rings
-/

open CategoryTheory AlgebraicGeometry

namespace FrobeniusSplitting

universe u

/-- A quasi-compact scheme locally of finite presentation over a finitely generated ℤ-algebra
is Noetherian, and its structure map is quasi-compact and quasi-separated. -/
theorem finiteType_int_scheme_properties {R : Type u} [CommRing R]
    [Algebra.FiniteType ℤ R] {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation f] :
    AlgebraicGeometry.IsNoetherian X ∧ QuasiCompact f ∧ QuasiSeparated f := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hnoeth : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  have : TopologicalSpace.NoetherianSpace X :=
    @AlgebraicGeometry.IsNoetherian.noetherianSpace X hnoeth
  refine ⟨hnoeth, ?_, ?_⟩
  · exact ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  · infer_instance

end FrobeniusSplitting
