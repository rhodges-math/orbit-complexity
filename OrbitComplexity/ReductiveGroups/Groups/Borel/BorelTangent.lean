import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelQuotientReduced
import OrbitComplexity.ReductiveGroups.Groups.Borel.BorelPointsSolvable
import OrbitComplexity.ReductiveGroups.Groups.Tangents.SolvableTangent
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupTangentInclusion
import OrbitComplexity.ReductiveGroups.Groups.RootCoordinates.BorelRootObstruction

/-!
# Borel Tangent

Solvability of the fixed original geometric Borel's tangent
and of its image in the original ambient tangent Lie algebra. -/

noncomputable section
namespace ReductiveGroups
open WithConv

universe u
variable {K B : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

/-- The quotient tangent of the given geometric Borel is solvable.
Its reducedness and point solvability are derived from the Borel condition. -/
theorem borelQuotient_tangent_isSolvable (J : TauCeti.HopfIdeal K B)
    (hJ : TauCeti.HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J) :
    LieAlgebra.IsSolvable (Derivation K (B ⧸ J.toIdeal)
      (TauCeti.Bialgebra.CounitAlgebra K (B ⧸ J.toIdeal) K)) := by
  let _ := borelQuotient_isReduced J hJ
  let _ := borelQuotient_points_isSolvable J hJ
  exact SolvableTangent.isSolvable_of_rational_points_isSolvable (K := K) (B := B ⧸ J.toIdeal)

/-- The Borel Lie subalgebra is the image of its quotient
differential in the tangent of the fixed original group. -/
theorem borel_tangentImage_isSolvable (J : TauCeti.HopfIdeal K B)
    (hJ : TauCeti.HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J) :
    LieAlgebra.IsSolvable
      (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  let _ := borelQuotient_tangent_isSolvable J hJ
  infer_instance

/-- The fixed Borel tangent cannot contain both original
character spaces for a nonidentity occurring torus character and its inverse. -/
theorem BorelTangent.not_contains_opposite_characterWeights
    [CharZero K] {ι : Type u} [Finite ι]
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (J : TauCeti.HopfIdeal K B)
    (hJ : TauCeti.HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (α : Multiplicative (ι →₀ ℤ))
    (hα : α ≠ 1) (hocc : affineGroupCharacterWeightSpace π α ≠ ⊥)
    (hpos : ∀ x : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K),
      x ∈ affineGroupCharacterWeightSpace π α →
      x ∈ (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range)
    (hneg : ∀ x : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K),
      x ∈ affineGroupCharacterWeightSpace π α⁻¹ →
      x ∈ (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range) :
    False := by
  let S := (TauCeti.derivationCompLieHom (B := K)
    (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  let _ : LieAlgebra.IsSolvable S := borel_tangentImage_isSolvable J hJ
  exact SolvableTangent.not_contains_opposite_characterWeights
    I hI π hπ hker hB S α hα hocc hpos hneg

end ReductiveGroups
