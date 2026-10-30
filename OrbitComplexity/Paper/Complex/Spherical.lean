import OrbitComplexity.GroupActions.Complexity.SphericalToric
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Spherical and toric varieties over the complex numbers

Sphericality is normality and zero complexity. A torus is its own Borel, and toricity is
equivalently sphericality for that torus or normality together with a dense torus orbit.
-/

open CategoryTheory GroupActions

namespace SchubertOrbits

/-- The spherical and toric definitions for complex algebraic varieties. -/
theorem spherical_toric_complex (G : ReductiveGroups.ReductiveGroupData ℂ) :
    (∀ (X : Variety ℂ) [ModObj (reductiveVariety G).toOver X.toOver],
      IsSpherical G X ↔ IrreducibleSpace X.scheme ∧ X.IsNormal ∧ complexity G X = 0) ∧
    TauCeti.HopfIdeal.IsBorel ℂ G.torusAlgebra.obj ⊥ ∧
    (∀ (Y : Variety ℂ) [ModObj (torusVariety G).toOver Y.toOver]
      [IrreducibleSpace Y.scheme],
      letI : ModObj (reductiveVariety G.torusData).toOver Y.toOver :=
        inferInstanceAs (ModObj (torusVariety G).toOver Y.toOver)
      torusComplexity G Y = complexity G.torusData Y ∧
      (IsToricVariety G Y ↔ IsSpherical G.torusData Y) ∧
      (IsToricVariety G Y ↔ Y.IsNormal ∧
        ∃ y : Y.points, Dense (Y.pointMap '' MulAction.orbit (torusVariety G).points y))) :=
  spherical_toric_definition G

end SchubertOrbits
