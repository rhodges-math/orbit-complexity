import OrbitComplexity.GroupActions.Rosenlicht.ReductiveComplexity
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Birational invariance of complex reductive complexity

An equivariant birational map between complex varieties preserves the minimum codimension
of Borel orbits.
-/

open CategoryTheory AlgebraicGeometry GroupActions

namespace SchubertOrbits

/-- An equivariant birational map preserves reductive complexity over the complex numbers. -/
theorem complexity_birational_complex (G : ReductiveGroups.ReductiveGroupData ℂ)
    (X Y : Variety ℂ) [ModObj (reductiveVariety G).toOver X.toOver]
    [ModObj (reductiveVariety G).toOver Y.toOver]
    [IrreducibleSpace X.scheme] [IrreducibleSpace Y.scheme]
    (f : X.scheme.PartialIso Y.scheme) (hf : f.IsOver X.toSpec Y.toSpec)
    (heq : RationalEquivariant (Variety.schemeTranslationHom (reductiveVariety G) X)
      (Variety.schemeTranslationHom (reductiveVariety G) Y) f.toPartialMap) :
    complexity G X = complexity G Y :=
  GroupActions.complexity_eq_of_birational G X Y f hf heq

end SchubertOrbits
