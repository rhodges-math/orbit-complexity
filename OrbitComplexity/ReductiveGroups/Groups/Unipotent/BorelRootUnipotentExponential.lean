import OrbitComplexity.ReductiveGroups.Groups.Unipotent.BorelRootUnipotentTangent
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupRootIntegration

/-!
# Borel Root Unipotent Exponential

Every tangent of the Borel's Ga-only subgroup has a
unique Ga integration in the original group and stays in the subgroup. -/

noncomputable section
namespace ReductiveGroups

open TauCeti

universe u
variable {K B ι : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (Bialgebra.CounitAlgebra K B K)
local notation "M" => Multiplicative (ι →₀ ℤ)

/-- Subgroup tangents integrate uniquely; matrix nilpotence and a
faithful representation are proved. -/
theorem BorelRootUnipotentExponential.existsUnique_borelRootUnipotentTangent
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (d : 𝔤)
    (hd : d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    ∃! x : B →ₐc[K] SymmetricAlgebra K K, gaAffineGroupTangent x = d := by
  obtain ⟨V, n, b, hρ⟩ := Comodule.exists_coordinateBialgHom_surjective (k := K) (H := B)
  exact AffineGroupRootIntegration.existsUnique_of_matrix_tangent_nilpotent n
    (Comodule.coordinateBialgHom b) hρ d
    ⟨n, BorelRootUnipotentTangent.matrix_pow_eq_zero J hJ π hπ n
      (Comodule.coordinateBialgHom b) d hd⟩

/-- The unique Ga map of any tangent in the original Ga-only subgroup. -/
def borelRootUnipotentGa
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (d : 𝔤)
    (hd : d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    B →ₐc[K] SymmetricAlgebra K K :=
  Classical.choose (BorelRootUnipotentExponential.existsUnique_borelRootUnipotentTangent J hJ π hπ d
    hd)

/-- The equality is

```lean
gaAffineGroupTangent (borelRootUnipotentGa J hJ π hπ d hd) = d
```
-/
@[simp] theorem borelRootUnipotentGa_tangent
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (d : 𝔤)
    (hd : d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    gaAffineGroupTangent (borelRootUnipotentGa J hJ π hπ d hd) = d :=
  (Classical.choose_spec
    (BorelRootUnipotentExponential.existsUnique_borelRootUnipotentTangent J hJ π hπ d hd)).1

/-- The equality is

```lean
∀ b ∈ borelRootUnipotentHopfIdeal J π hπ, borelRootUnipotentGa J hJ π hπ d hd b = 0
```
-/
theorem borelRootUnipotentGa_kills_ideal
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (d : 𝔤)
    (hd : d ∈ (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    ∀ b ∈ borelRootUnipotentHopfIdeal J π hπ, borelRootUnipotentGa J hJ π hπ d hd b = 0 := by
  apply (gaMorphism_kills_hopfIdeal_iff _ _).mpr
  rw [borelRootUnipotentGa_tangent]
  exact (tangent_mem_hopfQuotient_iff _ d).mp hd

/-- The original group point at parameter one of the unique integration. -/
def borelRootUnipotentExponential
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) : WithConv (B →ₐ[K] K) :=
  gaAffineGroupPoints (borelRootUnipotentGa J hJ π hπ d.val d.property)
    (Multiplicative.ofAdd 1)

/-- For these parameters,

```lean
borelRootUnipotentExponential J hJ π hπ d ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K)
```
-/
theorem borelRootUnipotentExponential_mem
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range) :
    borelRootUnipotentExponential J hJ π hπ d ∈
      CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ) (CommAlgCat.of K K) := by
  apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
  intro b hb
  change ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd 1)).ofConv (borelRootUnipotentGa J hJ π hπ d.val d.property b) = 0
  rw [borelRootUnipotentGa_kills_ideal J hJ π hπ d.val d.property b hb, map_zero]

/-- Every matrix representation computes this original-group point by the
finite associative exponential of the represented original tangent. -/
theorem borelRootUnipotentExponential_matrix
    (J : HopfIdeal K B) (hJ : HopfIdeal.IsBorel K (CommHopfAlgCat.of K B) J)
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (d : (derivationCompLieHom (B := K)
      (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
        (borelRootUnipotentHopfIdeal J π hπ)).hom).range)
    (n : ℕ) (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B) :
    (GeneralLinear.pointsMulEquiv n
      (AlgHom.mapDomain ρ (borelRootUnipotentExponential J hJ π hπ d)) :
        Matrix (Fin n) (Fin n) K) =
      associativeExponential (K := K) (affineGroupMatrixDifferential n ρ d.val) := by
  simpa only [borelRootUnipotentExponential, borelRootUnipotentGa_tangent, one_smul] using
    GaAffineGroupPoints.matrix_eq_exponential n
      (borelRootUnipotentGa J hJ π hπ d.val d.property) ρ 1

end ReductiveGroups
