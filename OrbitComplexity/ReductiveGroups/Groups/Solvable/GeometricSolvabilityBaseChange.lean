import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedGroupWordIdentity
import OrbitComplexity.ReductiveGroups.Groups.Solvable.DerivedWordClosure
import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange

/-!
# Geometric Solvability Base Change

Over an algebraically closed field, a reduced finite-type group's
rational solvability implies solvability over every value algebra and hence
geometric solvability after extension of the base field. -/

noncomputable section
namespace ReductiveGroups
open TauCeti WithConv

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [IsReduced B]

/-- For these parameters,

```lean
Group.IsSolvable (WithConv (B →ₐ[K] A))
```
-/
theorem affineGroupPoints_isSolvable_of_rational
    (h : Group.IsSolvable (WithConv (B →ₐ[K] K)))
    {A : Type*} [CommRing A] [Algebra K A] :
    Group.IsSolvable (WithConv (B →ₐ[K] A)) := by
  let := h
  obtain ⟨n, hn⟩ := DerivedWordSolvability.exists_identity_of_isSolvable
    (G := WithConv (B →ₐ[K] K))
  exact isSolvable_of_derivedGroupWord_identity n
    (derivedGroupWord_eq_one_of_rational n hn)

/-- The equality is

```lean
geometricallySolvablePointsCommHopfAlgProperty L
      (CommHopfAlgCat.baseChange (K := L) H)
```
-/
theorem GeometricallySolvable.baseChange_of_reduced
    (H : CommHopfAlgCat.{u} K) [Algebra.FiniteType K H] [IsReduced H]
    (hH : geometricallySolvablePointsCommHopfAlgProperty K H)
    (L : Type u) [Field L] [Algebra K L] :
    geometricallySolvablePointsCommHopfAlgProperty L
      (CommHopfAlgCat.baseChange (K := L) H) := by
  let : Group.IsSolvable (WithConv (H →ₐ[K] AlgebraicClosure K)) := hH
  have hrat : Group.IsSolvable (WithConv (H →ₐ[K] K)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := AlgHom.mapValue (H := H) (Algebra.ofId K (AlgebraicClosure K)))
      (AlgHom.mapValue_injective (algebraMap K (AlgebraicClosure K)).injective)
  let A := AlgebraicClosure L
  let : Algebra K A := Algebra.compHom A (algebraMap K L)
  let : SMul K A := Algebra.toSMul
  let : IsScalarTower K L A := IsScalarTower.of_algebraMap_eq' rfl
  let : Group.IsSolvable (WithConv (H →ₐ[K] A)) :=
    affineGroupPoints_isSolvable_of_rational hrat
  let e := AlgHom.baseChangePointsMulEquiv (k := K) (K := L) (A := H) (R := A)
  exact Group.isSolvable_of_isSolvable_injective
    (f := e.symm.toMonoidHom) e.symm.injective

end ReductiveGroups
