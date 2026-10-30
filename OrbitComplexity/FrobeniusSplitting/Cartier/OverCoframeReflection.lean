import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameReflection
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Batteries.Tactic.Lint

/-! # Reflection of coframes on ambient opens

The equivalence between module sheaves on an ambient open and on its open
subscheme carries local coframes to pulled-back line coframes. Injectivity
of the scalar map on functions reflects their equality.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules

namespace FrobeniusSplitting.OperatorSheaf

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Regard a coframe on an ambient open as a coframe on the open subscheme. -/
def coframeOnOpen {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (E : L.over U ≅ (unitModule X).over U) :
    (Scheme.Modules.pullback U.ι).obj L ≅ unitModule U.toScheme :=
  ((restrictFunctorIsoPullback U.ι).app L).symm ≪≫
    ((overFunctorEquiv U).app L).symm ≪≫ (overEquiv U).functor.mapIso E ≪≫
      (overFunctorEquiv U).app (unitModule X) ≪≫ restrictUnitIso U.ι

private theorem iso_map_injective {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Faithful] {M N : C} {P Q : D}
    (a : P ≅ F.obj M) (b : F.obj N ≅ Q) (E₁ E₂ : M ≅ N)
    (h : a ≪≫ F.mapIso E₁ ≪≫ b = a ≪≫ F.mapIso E₂ ≪≫ b) : E₁ = E₂ := by
  apply Iso.ext
  apply F.map_injective
  have hh : a.hom ≫ F.map E₁.hom ≫ b.hom =
      a.hom ≫ F.map E₂.hom ≫ b.hom := congrArg Iso.hom h
  exact (cancel_mono b.hom).mp ((cancel_epi a.hom).mp hh)

end FrobeniusSplitting.OperatorSheaf
