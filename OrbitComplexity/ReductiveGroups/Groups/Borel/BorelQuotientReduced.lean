import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelReducedBaseChange
import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange

/-!
# Borel Quotient Reduced

The quotient by a Borel Hopf ideal of a finite-type Hopf algebra over an
algebraically closed field is reduced: after base change to the algebraic
closure it is smooth (`Groups/BorelSmoothExtraction.lean`), and reducedness
descends along the base-change isomorphism (`Groups/BorelReducedBaseChange.lean`). -/

noncomputable section
namespace ReductiveGroups

set_option maxHeartbeats 400000

open TauCeti CategoryTheory

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

/-- For these parameters,

```lean
IsReduced (CommHopfAlgCat.quotient H J)
```
-/
theorem borelQuotient_isReduced_cat (H : CommHopfAlgCat K)
    [Algebra.FiniteType K H] (J : TauCeti.HopfIdeal K H)
    (hJ : TauCeti.HopfIdeal.IsBorel K H J) :
    IsReduced (CommHopfAlgCat.quotient H J) := by
  let C := AlgebraicClosure K
  exact isReduced_of_smooth_iso_baseChange
    (CommHopfAlgCat.quotient H J)
    (CommHopfAlgCat.quotient (CommHopfAlgCat.baseChange (K := C) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := C) J))
    (CommHopfAlgCat.quotientBaseChangeIso (K := C) J)
    ((TauCeti.HopfIdeal.isBorel_iff K H J).mp hJ).1

/-- The original fixed Borel quotient is reduced. -/
theorem borelQuotient_isReduced (J : TauCeti.HopfIdeal K B)
    (hJ : TauCeti.HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J) :
    IsReduced (B ⧸ J.toIdeal) := by
  exact borelQuotient_isReduced_cat (CommHopfAlgCat.of K B) J hJ

end ReductiveGroups
