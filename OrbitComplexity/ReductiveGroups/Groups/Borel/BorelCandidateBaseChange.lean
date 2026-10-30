import OrbitComplexity.ReductiveGroups.Groups.Solvable.GeometricSolvabilityBaseChange
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelMaximalityBaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed

/-!
# Borel Candidate Base Change

Borel candidates over the original algebraically closed field retain
their three geometric properties on scalar extension. Hence the pinned
geometric definition of Borel gives maximality over the original field. -/

noncomputable section
namespace ReductiveGroups
open TauCeti CategoryTheory
open scoped TensorProduct

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The equality is

```lean
HopfIdeal.IsBorelCandidate L (FiniteTypeCommHopfAlgCat.baseChange (K := L) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := L) J)
```
-/
theorem borelCandidate_baseChange_of_isAlgClosed
    (H : FiniteTypeCommHopfAlgCat.{u,u} K) (J : HopfIdeal K H)
    (hJ : HopfIdeal.IsBorelCandidate K H J)
    (L : Type u) [Field L] [Algebra K L] :
    HopfIdeal.IsBorelCandidate L (FiniteTypeCommHopfAlgCat.baseChange (K := L) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := L) J) := by
  let Q := CommHopfAlgCat.quotient H.obj J
  let Q' := CommHopfAlgCat.quotient (CommHopfAlgCat.baseChange (K := L) H.obj)
    (CommHopfAlgCat.baseChangeHopfIdeal (K := L) J)
  let e : Q' ≅ CommHopfAlgCat.baseChange (K := L) Q :=
    CommHopfAlgCat.quotientBaseChangeIso (K := L) J
  let : Algebra.Smooth K Q := hJ.1
  let : IsReduced Q := isReduced_of_smooth K Q
  have hs : smoothCommHopfAlgProperty L (CommHopfAlgCat.baseChange (K := L) Q) :=
    Algebra.Smooth.baseChange K Q L
  have hc : geometricallyConnectedCommHopfAlgProperty L
      (CommHopfAlgCat.baseChange (K := L) Q) :=
    geometricallyConnectedCommHopfAlgProperty.baseChange K L Q hJ.2.1
  have hv : geometricallySolvablePointsCommHopfAlgProperty L
      (CommHopfAlgCat.baseChange (K := L) Q) :=
    GeometricallySolvable.baseChange_of_reduced Q hJ.2.2 L
  exact ⟨(smoothCommHopfAlgProperty L).prop_of_iso e.symm hs,
    (geometricallyConnectedCommHopfAlgProperty L).prop_of_iso e.symm hc,
    (geometricallySolvablePointsCommHopfAlgProperty L).prop_of_iso e.symm hv⟩

/-- The inclusion is

```lean
J ≤ Q
```
-/
theorem borel_minimal_candidate_of_isAlgClosed
    (H : FiniteTypeCommHopfAlgCat.{u,u} K) (J Q : HopfIdeal K H)
    (hJ : HopfIdeal.IsBorel K H.obj J) (hQJ : Q ≤ J)
    (hQ : HopfIdeal.IsBorelCandidate K H Q) : J ≤ Q := by
  apply borel_minimal_baseChangeCandidate H J Q hJ hQJ
  exact borelCandidate_baseChange_of_isAlgClosed H Q hQ (AlgebraicClosure K)

end ReductiveGroups
