import OrbitComplexity.GroupActions.Rosenlicht.OrbitMaximum
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Invariant rational functions over the complex numbers

The minimum orbit codimension agrees with the transcendence degree of the invariant
function field for an irreducible acting group and irreducible variety.
-/

open CategoryTheory AlgebraicGeometry

namespace SchubertOrbits

/-- Complex orbit complexity is the transcendence degree of invariant rational functions. -/
theorem invariantComplexity_complex (H X : GroupActions.Variety ℂ)
    [GrpObj H.toOver] [ModObj H.toOver X.toOver]
    [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme] :
    letI : X.scheme.Over (Spec (.of ℂ)) := ⟨X.toSpec⟩
    letI : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
    GroupActions.minOrbitCodim H X =
      (Algebra.trdeg ℂ (GroupActions.Variety.invariantField H X)).toNat :=
  GroupActions.Variety.minOrbitCodim_eq_trdeg H X

end SchubertOrbits
