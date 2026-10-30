import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Borel Reduced Base Change

Geometric Borel solvability and smoothness returned to the fixed original
Hopf quotient, with no replacement of its defining ideal. -/

noncomputable section
namespace ReductiveGroups

set_option maxHeartbeats 400000

open TauCeti CategoryTheory WithConv
open scoped TensorProduct

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

/-- Smoothness after algebraic-closure base change detects reducedness of the
original coordinate ring by its injection into the scalar extension. -/
theorem isReduced_of_baseChange_smooth
    (Q : CommHopfAlgCat K)
    (hs : smoothCommHopfAlgProperty (AlgebraicClosure K)
      (CommHopfAlgCat.baseChange (K := AlgebraicClosure K) Q)) :
    IsReduced Q := by
  let C := AlgebraicClosure K
  let _ : Algebra.Smooth C (C ⊗[K] Q) := hs
  let _ : IsReduced (C ⊗[K] Q) := TauCeti.isReduced_of_smooth C _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight (R := K) (A := C) (B := Q)).toRingHom
    (Algebra.TensorProduct.includeRight_injective
      (A := C) (B := Q) (FaithfulSMul.algebraMap_injective K C))

/-- For these parameters,

```lean
IsReduced Q
```
-/
theorem isReduced_of_smooth_iso_baseChange
    (Q : CommHopfAlgCat K)
    (Q' : CommHopfAlgCat (AlgebraicClosure K))
    (e : Q' ≅ CommHopfAlgCat.baseChange (K := AlgebraicClosure K) Q)
    (hs : smoothCommHopfAlgProperty (AlgebraicClosure K) Q') :
    IsReduced Q := by
  apply isReduced_of_baseChange_smooth Q
  exact (smoothCommHopfAlgProperty (AlgebraicClosure K)).prop_of_iso e hs

end ReductiveGroups
