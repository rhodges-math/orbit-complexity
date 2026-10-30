import OrbitComplexity.ReductiveGroups.Groups.Representatives.WeylRepresentative
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootSystemBridge
import OrbitComplexity.ReductiveGroups.Groups.Cells.RankOneCellClosure
import OrbitComplexity.ReductiveGroups.Roots.Inversions.Inversions

/-!
# Schubert Cell Defs

The flag space, Schubert cells and Schubert varieties of the original
reductive group, on `K`-points.

* The flag space is the coset space `G(K) ⧸ B(K)` of the `K`-points of the
  original Borel, with the quotient of the Zariski topology on `G(K)`
  (`PointFlagSpace`). Over an algebraically closed field this is the space of
  closed points of the flag variety with its Zariski topology.
* For `w` in the Weyl group of the root system, with representative
  `ẇ = weylRepresentative … (borelRootBase …) w` in the torus normalizer, the
  Schubert cell is `X_w° = B ẇ B / B` and the Schubert variety is its closure
  `X_w`.
* `U_w` is `U_S` for the Borel root characters `S` whose roots are left
  inversions of `w`. -/

noncomputable section
namespace ReductiveGroups

open TauCeti LieAlgebra LieAlgebra.IsKilling LieModule

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

/-- The `K`-points of the Borel. -/
abbrev borelPointsSubgroup (J : HopfIdeal K B) : Subgroup (WithConv (B →ₐ[K] K)) :=
  CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B) J (CommAlgCat.of K K)

/-- The flag space `G(K) ⧸ B(K)`, with the quotient Zariski topology. -/
abbrev FlagPoints (J : HopfIdeal K B) : Type u :=
  WithConv (B →ₐ[K] K) ⧸ borelPointsSubgroup J

/-- The Bruhat cell `B n B / B` of a point `n`. -/
def bruhatCellPoints (J : HopfIdeal K B) (n : WithConv (B →ₐ[K] K)) : Set (FlagPoints J) :=
  QuotientGroup.mk '' pointDoubleCoset (borelPointsSubgroup J) n

section Weyl

variable (I J : HopfIdeal K B) (hJI : J ≤ I)
  (hI : HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
  (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
  (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) (hπ : Function.Surjective π)
  (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
  (hB : reductiveCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.of K B))

/-- The representative `ẇ` of a Weyl element, for the Borel base. -/
def borelWeylRepresentative :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).weylGroup →
      WithConv (B →ₐ[K] K) :=
  fun w => weylRepresentative I hI π hπ hker hB (borelRootBase I J hJI hI hJ π hπ hker hB) w

/-- The Schubert cell `X_w° = B ẇ B / B`. -/
def schubertCellPoints :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).weylGroup →
      Set (FlagPoints J) :=
  fun w => bruhatCellPoints J (borelWeylRepresentative I J hJI hI hJ π hπ hker hB w)

/-- The Schubert variety `X_w`, the closure of `X_w°` in the flag space. -/
def schubertVarietyPoints :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).weylGroup →
      Set (FlagPoints J) :=
  fun w => closure (schubertCellPoints I J hJI hI hJ π hπ hker hB w)

/-- The Borel root characters whose roots are left inversions of `w`. -/
def inversionCharacterSet :
    letI := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
    letI := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
    letI := ReductiveTorusRootSystem.tangent_centerQuotient_isKilling hB
    letI := ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan I hI π hπ hker hB
    (rootSystem (centerQuotientCartan (diagonalizableTangentImage π))).weylGroup →
      Set (borelRootCharacterIndex J π) :=
  fun w => {k | ReductiveCharacterRoots.characterCenterQuotientRootEquiv I hI π hπ hker hB
    (borelRootCharacterOccurring J π k) ∈
      leftRootInversionIndices (borelRootBase I J hJI hI hJ π hπ hker hB) w}

end Weyl

end ReductiveGroups
