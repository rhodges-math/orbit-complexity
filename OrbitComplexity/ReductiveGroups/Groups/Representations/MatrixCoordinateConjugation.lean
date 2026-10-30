import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupConjugationMorphism
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupAdjointMatrix
import OrbitComplexity.ReductiveGroups.Lie.Roots.MatrixBasisConjugation

/-!
# Matrix Coordinate Conjugation

A change of matrix basis is a coordinate Hopf representation
of the same original affine group, with the conjugated differential. -/

noncomputable section
namespace ReductiveGroups

open TauCeti WithConv

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- Conjugate a matrix representation by a fixed invertible matrix. -/
def matrixConjugateCoordinate (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (P : Matrix.GeneralLinearGroup (Fin n) K) :
    GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B :=
  ρ.comp (affineGroupConjugationBialgHom ((GeneralLinear.pointsMulEquiv n).symm P))

/-- The map is surjective:

```lean
Function.Surjective (matrixConjugateCoordinate n ρ P)
```
-/
theorem matrixConjugateCoordinate_surjective (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ) (P : Matrix.GeneralLinearGroup (Fin n) K) :
    Function.Surjective (matrixConjugateCoordinate n ρ P) :=
  hρ.comp (affineGroupConjugationBialgEquiv
    ((GeneralLinear.pointsMulEquiv n).symm P)).surjective

/-- The differential of the conjugated coordinate representation is
matrix conjugation of the original differential. -/
theorem AffineGroupMatrixDifferential.conjugate_coordinate (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (P : Matrix.GeneralLinearGroup (Fin n) K)
    (d : Derivation K B (Bialgebra.CounitAlgebra K B K)) :
    affineGroupMatrixDifferential n (matrixConjugateCoordinate n ρ P) d =
      (P : Matrix (Fin n) (Fin n) K) * affineGroupMatrixDifferential n ρ d *
        (P⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) := by
  rw [affineGroupMatrixDifferential_apply, matrixConjugateCoordinate,
    derivationComp_comp, LinearMap.comp_apply,
    DerivationComp.conjugation,
    generalLinear_tangentMatrix_adDerivation]
  simp only [generalLinearCounitPointsMulEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, affineGroupMatrixDifferential_apply]

/-- Any prescribed basis change of a represented matrix Lie action is
realized by another coordinate representation of the original group. -/
theorem exists_matrixCoordinate_in_basis (n : ℕ)
    (ρ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (b : Module.Basis (Fin n) K (Fin n → K)) :
    ∃ σ : GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B,
      (Function.Surjective ρ → Function.Surjective σ) ∧
      ∀ d : Derivation K B (Bialgebra.CounitAlgebra K B K),
        affineGroupMatrixDifferential n σ d =
          LinearMap.toMatrix b b (Matrix.toLin' (affineGroupMatrixDifferential n ρ d)) := by
  obtain ⟨P, hP⟩ := exists_matrixBasisConjugation n b
  refine ⟨matrixConjugateCoordinate n ρ P,
    fun hρ => matrixConjugateCoordinate_surjective n ρ hρ P, ?_⟩
  intro d
  rw [AffineGroupMatrixDifferential.conjugate_coordinate, hP]

end ReductiveGroups
