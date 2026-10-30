import OrbitComplexity.ReductiveGroups.Groups.Tangents.AffineGroupMatrixDifferential
import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding

/-!
# Finite Type Affine Group Differential

Finite-dimensional faithful tangent representations of the original
finite-type affine group. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B]

/-- Finite type makes the tangent Lie algebra finite-dimensional. -/
theorem finiteTypeAffineGroup_tangent_finite :
    Module.Finite K (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) := by
  exact Module.Finite.equiv (Derivation.cotangentLinearEquiv
    (R := K) (A := B) (B := K))

/-- Every finite type affine group admits a faithful finite-dimensional tangent representation. -/
theorem FiniteTypeAffineGroup.exists_injective_matrixDifferential :
    ∃ (n : ℕ) (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B),
      Function.Surjective ρ ∧ Function.Injective (affineGroupMatrixDifferential n ρ) := by
  obtain ⟨M, n, b, hρ⟩ :=
    TauCeti.Comodule.exists_coordinateBialgHom_surjective (k := K) (H := B)
  exact ⟨n, TauCeti.Comodule.coordinateBialgHom (H := B) b, hρ,
    AffineGroupMatrixDifferential.injective_of_surjective n _ hρ⟩

end ReductiveGroups
