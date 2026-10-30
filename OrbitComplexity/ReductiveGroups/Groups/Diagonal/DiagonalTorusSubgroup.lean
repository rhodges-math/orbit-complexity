import OrbitComplexity.ReductiveGroups.Groups.Diagonal.DiagonalMatrixTorus
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupIntersectionTangent
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
import TauCeti.Algebra.Bialgebra.GroupLike.Map

/-!
# Diagonal Torus Subgroup

The defining ideal and exact tangent criterion for the concrete
diagonal torus in the general-linear group. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K : Type u} [Field K] (n : ℕ)

/-- The Hopf ideal of the coordinate Hopf algebra of `GLₙ` cutting out the diagonal torus: the
kernel of the surjective coordinate map `diagonalTorusCoordinateMap`. -/
def diagonalMatrixHopfIdeal :
    TauCeti.HopfIdeal K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) :=
  TauCeti.HopfIdeal.kerOfSurjective
    (diagonalTorusCoordinateMap (R := K) (N := n)).hom
    diagonalTorusCoordinateMap_surjective

/-- The equality is

```lean
TauCeti.DiagonalizableGroup.groupLikeSpannedProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.of K
          (TauCeti.GeneralLinear.coordinateHopfAlgebra K n))
        (diagonalMatrixHopfIdeal (K := K) n))
```
-/
theorem DiagonalMatrixHopfIdeal.quotient_groupLikeSpanned :
    TauCeti.DiagonalizableGroup.groupLikeSpannedProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient
        (TauCeti.FiniteTypeCommHopfAlgCat.of K
          (TauCeti.GeneralLinear.coordinateHopfAlgebra K n))
        (diagonalMatrixHopfIdeal (K := K) n)) := by
  let δ := (diagonalTorusCoordinateMap (R := K) (N := n)).hom
  let e := TauCeti.HopfIdeal.kerLiftBialgEquiv δ diagonalTorusCoordinateMap_surjective
  exact TauCeti.GroupLike.groupLikeSetSpan_eq_top_of_surjective
    e.symm.toBialgHom e.symm.surjective
    (TauCeti.MonoidAlgebra.groupLikeSetSpan_eq_top K
      (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))

/-- The equivalence is

```lean
d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
        (diagonalMatrixHopfIdeal (K := K) n)).hom).range ↔
      d ∈ (TauCeti.derivationCompLieHom (B := K)
        (diagonalTorusCoordinateMap (R := K) (N := n)).hom).range
```
-/
theorem DiagonalTorusSubgroup.mem_diagonalMatrixHopfQuotient_iff
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K)) :
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
        (diagonalMatrixHopfIdeal (K := K) n)).hom).range ↔
      d ∈ (TauCeti.derivationCompLieHom (B := K)
        (diagonalTorusCoordinateMap (R := K) (N := n)).hom).range := by
  rw [tangent_mem_hopfQuotient_iff, tangent_mem_range_iff_kills_kernel _
    diagonalTorusCoordinateMap_surjective]
  apply forall_congr'
  intro a
  rw [diagonalMatrixHopfIdeal, TauCeti.HopfIdeal.mem_kerOfSurjective]

/-- No choices of weights or diagonal coordinates enter this criterion:
the tangent lies in the diagonal torus exactly when its matrix is
diagonal. The empty matrix is included. -/
theorem DiagonalTorusSubgroup.diagonalMatrixHopfQuotient_iff_matrix
    (d : Derivation K (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
      (TauCeti.Bialgebra.CounitAlgebra K
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n) K)) :
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient
        (TauCeti.GeneralLinear.coordinateHopfAlgebra K n)
        (diagonalMatrixHopfIdeal (K := K) n)).hom).range ↔
      ∀ i j : Fin n, i ≠ j → TauCeti.GeneralLinear.tangentMatrix n d i j = 0 := by
  rw [DiagonalTorusSubgroup.mem_diagonalMatrixHopfQuotient_iff]
  constructor
  · rintro ⟨e, rfl⟩ i j hij
    exact (diagonalTorus_tangentMatrix_apply e i j).trans (ite_eq_right hij)
  · intro hd
    obtain ⟨e, he⟩ := DiagonalTorus.tangentMatrix_surjective_diagonal
      (fun i : Fin n => TauCeti.GeneralLinear.tangentMatrix n d i i)
    refine ⟨e, ?_⟩
    apply (TauCeti.GeneralLinear.tangentLinearEquivMatrix (R := K) (B := K) n).injective
    change TauCeti.GeneralLinear.tangentMatrix n
      (TauCeti.derivationComp (B := K)
        (diagonalTorusCoordinateMap (R := K) (N := n)).hom e) =
      TauCeti.GeneralLinear.tangentMatrix n d
    rw [he]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hd i j hij]

end ReductiveGroups
