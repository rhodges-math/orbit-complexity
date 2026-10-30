import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupIntersectionTangent
import OrbitComplexity.ReductiveGroups.Groups.Diagonal.MaximalTorusLieCartan
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CartanQuotient

/-!
# Closed Subgroup Tangent Inclusion

Subgroup containment preserves tangent containment. In
particular, a subgroup containing the fixed maximal torus contains the
center of the reductive tangent Lie algebra. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

/-- Inclusion of closed subgroups reverses inclusion of their defining
ideals, and preserves inclusion of the quotient tangent images. -/
theorem hopfQuotient_tangentImage_antitone
    (I J : TauCeti.HopfIdeal K B) (hJI : J ≤ I) :
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range ≤
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  intro d hd
  apply (tangent_mem_hopfQuotient_iff J d).mpr
  intro b hb
  exact (tangent_mem_hopfQuotient_iff I d).mp hd b (hJI hb)

/-- Any original closed subgroup containing the fixed maximal torus
contains the center of the reductive tangent Lie algebra. -/
theorem MaximalTorusContaining.tangent_contains_center
    [IsAlgClosed K] [CharZero K] [Algebra.FiniteType K B]
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B))
    (J : TauCeti.HopfIdeal K B) (hJI : J ≤ I) :
    (LieAlgebra.center K
      (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) : LieSubalgebra K _) ≤
      (TauCeti.derivationCompLieHom (B := K)
        (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range := by
  let _ := reductive_maximalTorus_tangent_isCartan I hI hB
  exact (center_le_cartan _).trans (hopfQuotient_tangentImage_antitone I J hJI)

end ReductiveGroups
