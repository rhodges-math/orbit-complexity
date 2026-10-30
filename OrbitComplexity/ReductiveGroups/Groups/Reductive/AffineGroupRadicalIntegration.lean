import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupRootIntegration
import OrbitComplexity.ReductiveGroups.Lie.Exponential.AssociativeRadicalNilpotence

/-!
# Affine Group Radical Integration

Integrate the radical bracket in the original finite-type affine group. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

private abbrev affineTangent :=
  Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- Every tangent in the `[tangent, radical tangent]` integrates
uniquely to an additive-group morphism of the original affine group.
The faithful matrix differential is constructed from finite type. -/
theorem AffineGroupRadicalIntegration.existsUnique_of_mem_radicalBracket
    (d : affineTangent (K := K) (B := B))
    (hd : d ∈ (⁅(⊤ : LieIdeal K (affineTangent (K := K) (B := B))),
      LieAlgebra.radical K (affineTangent (K := K) (B := B))⁆ :
        LieIdeal K (affineTangent (K := K) (B := B)))) :
    ∃! x : B →ₐc[K] SymmetricAlgebra K K, gaAffineGroupTangent x = d := by
  let : Module.Finite K (affineTangent (K := K) (B := B)) :=
    finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  obtain ⟨n, ρ, hρ, _⟩ :=
    FiniteTypeAffineGroup.exists_injective_matrixDifferential (K := K) (B := B)
  apply AffineGroupRootIntegration.existsUnique_of_matrix_tangent_nilpotent n ρ hρ d
  exact AssociativeRadicalNilpotence.image_isNilpotent_of_mem_radicalBracket
    (affineGroupMatrixDifferential n ρ) hd

/-- The canonical additive-group morphism associated to a tangent in the
radical bracket. -/
def radicalVectorGaMorphism
    (d : affineTangent (K := K) (B := B))
    (hd : d ∈ (⁅(⊤ : LieIdeal K (affineTangent (K := K) (B := B))),
      LieAlgebra.radical K (affineTangent (K := K) (B := B))⁆ :
        LieIdeal K (affineTangent (K := K) (B := B)))) :
    B →ₐc[K] SymmetricAlgebra K K :=
  Classical.choose (AffineGroupRadicalIntegration.existsUnique_of_mem_radicalBracket d hd)

/-- The equality is

```lean
gaAffineGroupTangent (radicalVectorGaMorphism d hd) = d
```
-/
@[simp] theorem radicalVectorGaMorphism_tangent
    (d : affineTangent (K := K) (B := B))
    (hd : d ∈ (⁅(⊤ : LieIdeal K (affineTangent (K := K) (B := B))),
      LieAlgebra.radical K (affineTangent (K := K) (B := B))⁆ :
        LieIdeal K (affineTangent (K := K) (B := B)))) :
    gaAffineGroupTangent (radicalVectorGaMorphism d hd) = d :=
  (Classical.choose_spec (AffineGroupRadicalIntegration.existsUnique_of_mem_radicalBracket d hd)).1

end ReductiveGroups
