import OrbitComplexity.ReductiveGroups.Groups.Centralizers.TorusCentralizerJordan
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupAdjointMatrix

/-!
# Torus Centralizer Matrix

Membership in the torus-centralizer tangent is equivalent to
commuting with the represented torus points in a faithful embedding. -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B : Type u} [Field K] [CommRing B] [HopfAlgebra K B]

/-- The equivalence is

```lean
affineGroupAdjointRepresentation g d = d ↔
      Commute (TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain ρ g) : Matrix (Fin n) (Fin n) K)
        (affineGroupMatrixDifferential n ρ d)
```
-/
theorem AffineGroupAdjoint.fixed_iff_matrix_commute
    (n : ℕ) (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ) (g : WithConv (B →ₐ[K] K))
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    affineGroupAdjointRepresentation g d = d ↔
      Commute (TauCeti.GeneralLinear.pointsMulEquiv n
        (TauCeti.AlgHom.mapDomain ρ g) : Matrix (Fin n) (Fin n) K)
        (affineGroupMatrixDifferential n ρ d) := by
  rw [← (AffineGroupMatrixDifferential.injective_of_surjective n ρ hρ).eq_iff]
  rw [affineGroupAdjointRepresentation_apply, affineGroupMatrixDifferential_adjoint,
    Units.mul_inv_eq_iff_eq_mul]
  rfl

variable {ι : Type u} [IsAlgClosed K]
  [Algebra.FiniteType K B] [Finite ι]

/-- The equivalence is

```lean
d ∈ torusCentralizerTangent π ↔
      ∀ g : WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K),
        Commute (TauCeti.GeneralLinear.pointsMulEquiv n
          (TauCeti.AlgHom.mapDomain ρ (TauCeti.AlgHom.mapDomain π g)) :
            Matrix (Fin n) (Fin n) K)
          (affineGroupMatrixDifferential n ρ d)
```
-/
theorem torusCentralizer_mem_iff_matrix_commute
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (n : ℕ) (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    d ∈ torusCentralizerTangent π ↔
      ∀ g : WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K),
        Commute (TauCeti.GeneralLinear.pointsMulEquiv n
          (TauCeti.AlgHom.mapDomain ρ (TauCeti.AlgHom.mapDomain π g)) :
            Matrix (Fin n) (Fin n) K)
          (affineGroupMatrixDifferential n ρ d) := by
  change d ∈ (TauCeti.derivationCompLieHom (B := K)
    (TauCeti.CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B)
      (torusConjugationFixedHopfIdeal π)).hom).range ↔ _
  rw [tangent_mem_torusConjugationFixed_iff,
    TorusPointFixedWeights.mem_one_iff_fixed_points]
  apply forall_congr'
  intro g
  exact AffineGroupAdjoint.fixed_iff_matrix_commute n ρ hρ _ d

end ReductiveGroups
