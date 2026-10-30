import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusGaGeneratorFamily
import OrbitComplexity.ReductiveGroups.Groups.Representations.FaithfulMatrixBasis
import OrbitComplexity.ReductiveGroups.Groups.Representations.MatrixInvariantFlags

/-!
# Torus Ga Solvable Candidate

A common upper triangular basis for the torus and Ga tangents
gives a smooth connected solvable closed subgroup of the original group. -/

noncomputable section
namespace ReductiveGroups
open Module WithConv CategoryTheory

universe u
variable {K B ι σ : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

/-- For these parameters,

```lean
TauCeti.HopfIdeal.IsBorelCandidate K (TauCeti.FiniteTypeCommHopfAlgCat.of K B)
      (TauCeti.CommHopfAlgCat.commonKernelHopfIdeal (torusGaGeneratorFamily π x))
```
-/
theorem TorusGaGenerated.borelCandidate_of_triangular_tangents
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (x : σ → B →ₐc[K] SymmetricAlgebra K K)
    (n : ℕ) (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ) (b : Basis (Fin n) K (Fin n → K))
    (hT : ∀ h : Derivation K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) K),
      matrixUpperGap 0 (LinearMap.toMatrix b b
        (Matrix.toLin' (affineGroupMatrixDifferential n (π.comp ρ) h))))
    (hX : ∀ i : σ, matrixUpperGap 0 (LinearMap.toMatrix b b
      (Matrix.toLin' (affineGroupMatrixDifferential n ρ (gaAffineGroupTangent (x i)))))) :
    TauCeti.HopfIdeal.IsBorelCandidate K (TauCeti.FiniteTypeCommHopfAlgCat.of K B)
      (TauCeti.CommHopfAlgCat.commonKernelHopfIdeal (torusGaGeneratorFamily π x)) := by
  let _ := fun j : Option σ => torusGaGeneratorCodomain_finiteType π hπ j
  let _ := fun j : Option σ => torusGaGeneratorCodomain_isDomain (K := K) (ι := ι) j
  let _ : ∀ j, IsReduced (torusGaGeneratorCodomain K ι σ j) := fun _ => inferInstance
  let _ : ∀ j, ConnectedSpace (PrimeSpectrum (torusGaGeneratorCodomain K ι σ j)) :=
    fun _ => inferInstance
  apply CommonKernelQuotient.borelCandidate_of_matrixBasis (CommHopfAlgCat.of K B)
    (torusGaGeneratorCodomain K ι σ) (torusGaGeneratorFamily π x) ρ hρ b
  intro j p
  cases j with
  | none =>
      change WithConv (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) →ₐ[K] K) at p
      have hp := torusMatrixPoint_upper_of_tangents_upper (π.comp ρ) b hT p
      rw [TauCeti.AlgHom.mapDomain_comp] at hp
      exact hp
  | some i =>
      obtain ⟨t, rfl⟩ :=
        (TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm.surjective p
      exact GaAffineGroupMatrixPoint.upper_of_tangent_upper (x i) ρ b (hX i)
        (Multiplicative.toAdd t)

end ReductiveGroups
