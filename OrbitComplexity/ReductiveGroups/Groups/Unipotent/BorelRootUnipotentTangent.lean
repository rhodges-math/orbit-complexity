import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentSubgroup
import OrbitComplexity.ReductiveGroups.Groups.Tangents.SolvableGaGeneratedTangent
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusTangentNilpotence

/-!
# Borel Root Unipotent Tangent

Exact tangent control for the Ga-only subgroup of the Borel. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Every matrix representation sends a tangent of the Borel's
Ga-only subgroup to a nilpotent matrix, with matrix-size exponent. -/
theorem BorelRootUnipotentTangent.matrix_pow_eq_zero
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (d : 𝔤)
    (hd : d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    (affineGroupMatrixDifferential n ρ d) ^ n = 0 := by
  let S := (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) J).hom).range
  let : LieAlgebra.IsSolvable S := borel_tangentImage_isSolvable J hJ
  exact SolvableGaGeneratedTangent.matrix_pow_eq_zero (borelRootVectorGa J π hπ) S
    (fun r => by rw [borelRootVectorGa_tangent]; exact r.2.property.2.2) n ρ d hd

/-- The tangent of the Ga-only Borel subgroup contains no nonzero
direction of the torus. A faithful representation is constructed. -/
theorem BorelRootUnipotentTangent.inf_torus_eq_bot
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) :
    (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range ⊓
      diagonalizableTangentImage π = ⊥ := by
  apply bot_unique
  intro d hd
  change d = 0
  obtain ⟨V, n, b, hρ⟩ := Comodule.exists_coordinateBialgHom_surjective (k := K) (H := B)
  apply TorusTangent.eq_zero_of_faithful_matrix_nilpotent π n
    (Comodule.coordinateBialgHom b) hρ d hd.2
  exact ⟨n, BorelRootUnipotentTangent.matrix_pow_eq_zero J hJ π hπ n
    (Comodule.coordinateBialgHom b) d hd.1⟩

end ReductiveGroups
