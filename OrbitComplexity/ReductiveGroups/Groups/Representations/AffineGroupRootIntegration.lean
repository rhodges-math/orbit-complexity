import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMorphismDescent
import OrbitComplexity.ReductiveGroups.Groups.Additive.NilpotentMatrixGaMorphism
import OrbitComplexity.ReductiveGroups.Groups.Tangents.FiniteTypeAffineGroupDifferential
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPointInjectivity
import OrbitComplexity.ReductiveGroups.Lie.Exponential.AssociativeRootNilpotence

/-!
# Affine Group Root Integration

Integrate nilpotent and nonzero-weight tangents inside the original
affine group.  -/

noncomputable section
namespace ReductiveGroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [HopfAlgebra K B]

/-- A tangent whose image in a closed matrix embedding is nilpotent integrates
uniquely to an additive-group coordinate morphism in the original group. -/
theorem AffineGroupRootIntegration.existsUnique_of_matrix_tangent_nilpotent
    (n : ℕ) (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : IsNilpotent (affineGroupMatrixDifferential n ρ d)) :
    ∃! x : B →ₐc[K] SymmetricAlgebra K K, gaAffineGroupTangent x = d := by
  let φ := nilpotentMatrixGaMorphism (affineGroupMatrixDifferential n ρ d) hd
  have hφ : gaAffineGroupTangent φ = TauCeti.derivationComp (B := K) ρ d := by
    apply (TauCeti.GeneralLinear.tangentLieEquivMatrix n).injective
    change TauCeti.GeneralLinear.tangentMatrix n (gaAffineGroupTangent φ) =
      affineGroupMatrixDifferential n ρ d
    exact nilpotentMatrixGaMorphism_tangent (affineGroupMatrixDifferential n ρ d) hd
  obtain ⟨x, hx, _⟩ := GaMorphismDescent.existsUnique_of_tangent_factor ρ hρ φ d hφ
  refine ⟨x, hx.2, ?_⟩
  intro y hy
  exact gaMorphism_ext_of_tangent_eq y x (hy.trans hx.2.symm)

/-- Every nonzero-weight root vector integrates uniquely to an
additive-group morphism of the original finite-type affine group. Matrix
nilpotence is derived from the root-space condition in every finite Lie
representation. The zero vector is allowed and gives the trivial morphism. -/
theorem existsUnique_gaMorphism_of_mem_rootSpace
    [IsAlgClosed K] [Algebra.FiniteType K B]
    (H : LieSubalgebra K (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)))
    [LieRing.IsNilpotent H] (χ : H → K) (hχ : χ ≠ 0)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ LieAlgebra.rootSpace H χ) :
    ∃! x : B →ₐc[K] SymmetricAlgebra K K, gaAffineGroupTangent x = d := by
  obtain ⟨n, ρ, hρ, _⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := B)
  apply AffineGroupRootIntegration.existsUnique_of_matrix_tangent_nilpotent n ρ hρ d
  exact AssociativeRootNilpotence.image_isNilpotent_of_mem_rootSpace H
    (affineGroupMatrixDifferential n ρ) hχ hd

variable [IsAlgClosed K] [Algebra.FiniteType K B]

/-- The uniquely integrated additive-group morphism of a root vector. -/
def rootVectorGaMorphism
    (H : LieSubalgebra K (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)))
    [LieRing.IsNilpotent H] (χ : H → K) (hχ : χ ≠ 0)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ LieAlgebra.rootSpace H χ) : B →ₐc[K] SymmetricAlgebra K K :=
  Classical.choose (existsUnique_gaMorphism_of_mem_rootSpace H χ hχ d hd)

/-- The equality is

```lean
gaAffineGroupTangent (rootVectorGaMorphism H χ hχ d hd) = d
```
-/
@[simp] theorem rootVectorGaMorphism_tangent
    (H : LieSubalgebra K (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)))
    [LieRing.IsNilpotent H] (χ : H → K) (hχ : χ ≠ 0)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ LieAlgebra.rootSpace H χ) :
    gaAffineGroupTangent (rootVectorGaMorphism H χ hχ d hd) = d :=
  (Classical.choose_spec (existsUnique_gaMorphism_of_mem_rootSpace H χ hχ d hd)).1

/-- A nonzero root vector gives an injective point parametrization. -/
theorem rootVectorGaMorphism_points_injective
    (H : LieSubalgebra K (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)))
    [LieRing.IsNilpotent H] (χ : H → K) (hχ : χ ≠ 0)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K))
    (hd : d ∈ LieAlgebra.rootSpace H χ) (hd0 : d ≠ 0) :
    Function.Injective (gaAffineGroupPoints (rootVectorGaMorphism H χ hχ d hd)) := by
  apply GaAffineGroupPoints.injective_of_tangent_ne_zero
  simpa only [rootVectorGaMorphism_tangent] using hd0

end ReductiveGroups
