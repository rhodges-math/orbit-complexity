import OrbitComplexity.ReductiveGroups.Groups.Tangents.HopfAutomorphismFixedTangent
import OrbitComplexity.ReductiveGroups.Groups.Centralizers.TorusConjugationFixedSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusPointFixedWeights
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusZeroWeight

/-!
# Torus Centralizer Tangent

The tangent of the subgroup fixed by torus conjugation is the
identity-character weight space in the original ambient tangent algebra. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B] [Finite ι]

/-- The fixed subgroup's quotient differential has precisely the
identity-character weight space as its image. -/
theorem tangent_mem_torusConjugationFixed_iff
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (torusConjugationFixedHopfIdeal π)).hom).range ↔
      d ∈ affineGroupCharacterWeightSpace π 1 := by
  rw [torusConjugationFixedHopfIdeal,
    HopfAutomorphismFixedTangent.hopfAutomorphismFixed_iff_differential,
    TorusPointFixedWeights.mem_one_iff_fixed_points]
  apply forall_congr'
  intro g
  change (TauCeti.derivationComp (B := K)
    (affineGroupConjugationBialgHom (TauCeti.AlgHom.mapDomain π g)) d = d) ↔ _
  rw [DerivationComp.conjugation]
  rfl

/-- Equality of submodules, retaining the original coordinate quotient and
the original torus character action. -/
theorem TorusConjugationFixed.tangentImage_eq_identityWeight
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) :
    (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (torusConjugationFixedHopfIdeal π)).hom).range.toSubmodule =
      affineGroupCharacterWeightSpace π 1 := by
  ext d
  exact tangent_mem_torusConjugationFixed_iff π d

/-- In characteristic zero, the same image is the ordinary Lie centralizer
of the original embedded torus tangent. -/
theorem TorusCentralizerTangent.mem_torusConjugationFixed_iff_bracket [CharZero K]
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    d ∈ (TauCeti.derivationCompLieHom (B := K)
      (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (torusConjugationFixedHopfIdeal π)).hom).range ↔
      ∀ x : diagonalizableTangentImage π,
        ⁅(x : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)), d⁆ = 0 :=
  (tangent_mem_torusConjugationFixed_iff π d).trans
    (mem_affineGroupIdentityWeight_iff π hπ d)

end ReductiveGroups
