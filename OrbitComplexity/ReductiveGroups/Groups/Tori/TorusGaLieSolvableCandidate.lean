import OrbitComplexity.ReductiveGroups.Groups.Solvable.SolvableLieTriangularBasis
import OrbitComplexity.ReductiveGroups.Groups.Tori.TorusGaSolvableCandidate

/-!
# Torus Ga Lie Solvable Candidate

A solvable Lie subalgebra containing the torus and Ga tangents
produces a Borel candidate in the original affine group. -/

noncomputable section
namespace ReductiveGroups

open Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u
variable {K B ι σ : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

/-- For these parameters,

```lean
TauCeti.HopfIdeal.IsBorelCandidate K (TauCeti.FiniteTypeCommHopfAlgCat.of K B)
      (TauCeti.CommHopfAlgCat.commonKernelHopfIdeal (torusGaGeneratorFamily π x))
```
-/
theorem TorusGaGenerated.borelCandidate_of_solvable_tangents
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (x : σ → B →ₐc[K] SymmetricAlgebra K K)
    (n : ℕ) (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (S : LieSubalgebra K
      (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)))
    [LieAlgebra.IsSolvable S]
    (hT : diagonalizableTangentImage π ≤ S)
    (hX : ∀ i : σ, gaAffineGroupTangent (x i) ∈ S) :
    TauCeti.HopfIdeal.IsBorelCandidate K (TauCeti.FiniteTypeCommHopfAlgCat.of K B)
      (TauCeti.CommHopfAlgCat.commonKernelHopfIdeal (torusGaGeneratorFamily π x)) := by
  let fS : S →ₗ⁅K⁆ Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K]
      Module.End K (Fin n → K)).toAlgHom.toLieHom.comp
      ((affineGroupMatrixDifferential n ρ).comp S.incl)
  let _ : LieRingModule S (Fin n → K) :=
    LieRingModule.compLieHom (Fin n → K) fS
  let _ : LieModule K S (Fin n → K) :=
    LieModule.compLieHom (Fin n → K) fS
  have hact (z : S) (v : Fin n → K) :
      ⁅z, v⁆ = Matrix.toLin' (affineGroupMatrixDifferential n ρ (z : _)) v := by
    rfl
  obtain ⟨b, hb⟩ := SolvableLieTriangularBasis.exists_upperTriangular_matrix_basis K S n
  apply TorusGaGenerated.borelCandidate_of_triangular_tangents
    π hπ x n ρ hρ b
  · intro h i j hij
    have hz : TauCeti.derivationComp (B := K) π h ∈ S :=
      hT (show TauCeti.derivationComp (B := K) π h ∈
        diagonalizableTangentImage π from ⟨h, rfl⟩)
    let z : S := ⟨TauCeti.derivationComp (B := K) π h, hz⟩
    have hcomp : affineGroupMatrixDifferential n (π.comp ρ) h =
        affineGroupMatrixDifferential n ρ (z : _) := by
      rw [affineGroupMatrixDifferential_apply, affineGroupMatrixDifferential_apply]
      rw [TauCeti.derivationComp_comp, LinearMap.comp_apply]
    rw [LinearMap.toMatrix_apply, hcomp]
    change b.repr (Matrix.toLin'
      (affineGroupMatrixDifferential n ρ (z : _)) (b j)) i = 0
    rw [← hact z]
    exact hb z i j (by simpa using hij)
  · intro a i j hij
    let z : S := ⟨gaAffineGroupTangent (x a), hX a⟩
    rw [LinearMap.toMatrix_apply]
    change b.repr (Matrix.toLin'
      (affineGroupMatrixDifferential n ρ (z : _)) (b j)) i = 0
    rw [← hact z]
    exact hb z i j (by simpa using hij)

end ReductiveGroups
