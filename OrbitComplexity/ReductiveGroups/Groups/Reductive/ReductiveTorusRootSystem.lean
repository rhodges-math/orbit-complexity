import OrbitComplexity.ReductiveGroups.Groups.Diagonal.MaximalTorusLieCartan
import OrbitComplexity.ReductiveGroups.Groups.Reductive.ReductiveTangentRadical
import OrbitComplexity.ReductiveGroups.Lie.Cartan.CartanQuotient
import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Reductive Torus Root System

The original reductive group supplies the Killing and Cartan hypotheses
for the root system of its center quotient. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- Geometric reductivity of the original group gives a nondegenerate
Killing form on the tangent quotient by its center. -/
theorem ReductiveTorusRootSystem.tangent_centerQuotient_isKilling
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B)) :
    LieAlgebra.IsKilling K (𝔤 ⧸ LieAlgebra.center K 𝔤) := by
  let _ := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  let _ := reductive_tangent_hasCentralRadical hB
  exact centralRadical_centerQuotient_isKilling

/-- The image of the original maximal torus tangent is Cartan in the
center quotient, using its exact split coordinate map. -/
theorem ReductiveTorusRootSystem.coordinateCenterQuotient_isCartan
    [Finite ι]
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (hker : ∀ a : B, π a = 0 ↔ a ∈ I.toIdeal)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B)) :
    ((diagonalizableTangentImage π).map
      (centerQuotientLieHom (K := K))).IsCartanSubalgebra := by
  let _ := MaximalTorusLieCartan.maximalTorus_coordinateTangent_isCartan I hI π hπ hker hB
  apply cartan_map_of_surjective (centerQuotientLieHom (K := K))
    centerQuotientLieHom_surjective (diagonalizableTangentImage π)
  rw [centerQuotientLieHom_ker]
  exact center_le_cartan _

/-- Coordinate-free form: the fixed original torus quotient differential,
followed by the center quotient, has Cartan image. -/
theorem ReductiveTorusRootSystem.maximalTorus_centerQuotient_isCartan
    (I : TauCeti.HopfIdeal K B)
    (hI : TauCeti.HopfIdeal.IsMaximalTorus K (CommHopfAlgCat.of K B) I)
    (hB : TauCeti.reductiveCommHopfAlgProperty K
      (TauCeti.FiniteTypeCommHopfAlgCat.of K B)) :
    ((TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range.map
        (centerQuotientLieHom (K := K))).IsCartanSubalgebra := by
  let _ := reductive_maximalTorus_tangent_isCartan I hI hB
  apply cartan_map_of_surjective (centerQuotientLieHom (K := K))
    centerQuotientLieHom_surjective
  rw [centerQuotientLieHom_ker]
  exact center_le_cartan _

end ReductiveGroups
