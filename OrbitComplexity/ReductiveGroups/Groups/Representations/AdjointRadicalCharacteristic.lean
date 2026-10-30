import OrbitComplexity.ReductiveGroups.Lie.Roots.RadicalCharacteristic
import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointRepresentation
import OrbitComplexity.ReductiveGroups.Groups.Tangents.FiniteTypeAffineGroupDifferential
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Basic

/-!
# Adjoint Radical Characteristic

The original affine group's point adjoint action preserves the solvable
radical and its bracket with the tangent Lie algebra. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

private abbrev affineTangent :=
  Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- An ordinary group point acts by a Lie automorphism on the
original group's tangent derivations. -/
def affineGroupAdjointLieEquiv (g : WithConv (B →ₐ[K] K)) :
    affineTangent (K := K) (B := B) ≃ₗ⁅K⁆ affineTangent (K := K) (B := B) where
  toFun := affineGroupAdjointRepresentation g
  invFun := affineGroupAdjointRepresentation g⁻¹
  map_add' := (affineGroupAdjointRepresentation g).map_add
  map_smul' := (affineGroupAdjointRepresentation g).map_smul
  map_lie' := by
    intro d₁ d₂
    simpa only [affineGroupAdjointRepresentation_apply] using
      (Derivation.adDerivation_lie K
        ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K B K).symm g) d₁ d₂)
  left_inv := by
    intro d
    change affineGroupAdjointRepresentation g⁻¹
      (affineGroupAdjointRepresentation g d) = d
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  right_inv := by
    intro d
    change affineGroupAdjointRepresentation g
      (affineGroupAdjointRepresentation g⁻¹ d) = d
    rw [← Module.End.mul_apply, ← map_mul]
    simp

/-- The equality is

```lean
affineGroupAdjointLieEquiv g d = affineGroupAdjointRepresentation g d
```
-/
@[simp] theorem affineGroupAdjointLieEquiv_apply
    (g : WithConv (B →ₐ[K] K)) (d : affineTangent (K := K) (B := B)) :
    affineGroupAdjointLieEquiv g d = affineGroupAdjointRepresentation g d := rfl

variable [Algebra.FiniteType K B]

/-- Point adjoints preserve the solvable radical of the
tangent Lie algebra. -/
theorem affineGroupAdjoint_radical (g : WithConv (B →ₐ[K] K))
    (d : affineTangent (K := K) (B := B))
    (hd : d ∈ LieAlgebra.radical K (affineTangent (K := K) (B := B))) :
    affineGroupAdjointRepresentation g d ∈
      LieAlgebra.radical K (affineTangent (K := K) (B := B)) := by
  have := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  rw [← radical_map_lieEquiv (affineGroupAdjointLieEquiv g)]
  exact LieIdeal.mem_map (f := (affineGroupAdjointLieEquiv g).toLieHom) hd

/-- Point adjoints preserve `[𝔤, radical 𝔤]` inside the original
tangent Lie algebra. -/
theorem affineGroupAdjoint_bracket_radical (g : WithConv (B →ₐ[K] K))
    (d : affineTangent (K := K) (B := B))
    (hd : d ∈ ⁅(⊤ : LieIdeal K (affineTangent (K := K) (B := B))),
      LieAlgebra.radical K (affineTangent (K := K) (B := B))⁆) :
    affineGroupAdjointRepresentation g d ∈
      ⁅(⊤ : LieIdeal K (affineTangent (K := K) (B := B))),
        LieAlgebra.radical K (affineTangent (K := K) (B := B))⁆ := by
  have := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  rw [← bracket_radical_map_lieEquiv (affineGroupAdjointLieEquiv g)]
  exact LieIdeal.mem_map (f := (affineGroupAdjointLieEquiv g).toLieHom) hd

end ReductiveGroups
