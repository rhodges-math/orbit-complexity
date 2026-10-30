import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelQuotientReduced
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed

/-!
# Borel Geometric Properties

Smoothness and geometric connectedness of the fixed original Borel
quotient, descended from its pinned algebraic-closure definition. -/

noncomputable section
namespace ReductiveGroups

open TauCeti CategoryTheory

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

/-- For these parameters,

```lean
smoothCommHopfAlgProperty K (CommHopfAlgCat.quotient H J)
```
-/
theorem borelQuotient_smooth_cat (H : CommHopfAlgCat.{u} K)
    [Algebra.FiniteType K H] (J : HopfIdeal K H)
    (hJ : HopfIdeal.IsBorel K H J) :
    smoothCommHopfAlgProperty K (CommHopfAlgCat.quotient H J) := by
  let _ : IsReduced (CommHopfAlgCat.quotient H J) :=
    borelQuotient_isReduced_cat H J hJ
  exact smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced K
    (CommHopfAlgCat.quotient H J)

omit [IsAlgClosed K] in
/-- For these parameters,

```lean
geometricallyConnectedCommHopfAlgProperty K
      (CommHopfAlgCat.quotient H J)
```
-/
theorem borelQuotient_geometricallyConnected_cat (H : CommHopfAlgCat.{u} K)
    [Algebra.FiniteType K H] (J : HopfIdeal K H)
    (hJ : HopfIdeal.IsBorel K H J) :
    geometricallyConnectedCommHopfAlgProperty K
      (CommHopfAlgCat.quotient H J) := by
  let C := AlgebraicClosure K
  let Q := CommHopfAlgCat.quotient H J
  let Q' := CommHopfAlgCat.quotient
    (CommHopfAlgCat.baseChange (K := C) H)
    (CommHopfAlgCat.baseChangeHopfIdeal (K := C) J)
  let e : Q' ≅ CommHopfAlgCat.baseChange (K := C) Q :=
    CommHopfAlgCat.quotientBaseChangeIso (K := C) J
  have hc : geometricallyConnectedCommHopfAlgProperty C Q' :=
    ((HopfIdeal.isBorel_iff K H J).mp hJ).2.1
  have hbc : geometricallyConnectedCommHopfAlgProperty C
      (CommHopfAlgCat.baseChange (K := C) Q) :=
    (geometricallyConnectedCommHopfAlgProperty C).prop_of_iso e hc
  exact geometricallyConnectedCommHopfAlgProperty.of_baseChange K C Q hbc

/-- The same fixed original Borel quotient is smooth over the original
algebraically closed field. -/
theorem borelQuotient_smooth (J : HopfIdeal K B)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J) :
    smoothCommHopfAlgProperty K
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of K B) J) :=
  borelQuotient_smooth_cat (CommHopfAlgCat.of K B) J hJ

omit [IsAlgClosed K] in
/-- The same fixed original Borel quotient is geometrically connected. -/
theorem borelQuotient_geometricallyConnected (J : HopfIdeal K B)
    (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J) :
    geometricallyConnectedCommHopfAlgProperty K
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of K B) J) :=
  borelQuotient_geometricallyConnected_cat (CommHopfAlgCat.of K B) J hJ

end ReductiveGroups
