import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupAdjoint
import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointRepresentation
import OrbitComplexity.ReductiveGroups.Lie.Roots.Sl2AdjointReflection

/-!
# Ga Sl 2 Reflection

The rank-one reflection calculation is realized by a product of three
additive-subgroup points in the original affine group. -/

noncomputable section
namespace ReductiveGroups
open LieAlgebra

private theorem nilpotentLieAdjointExponential_eq_scaled
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    (x : L) (hx : IsNilpotent (ad K L x)) (t : K) :
    nilpotentLieAdjointExponential x hx t =
      nilpotentAdjointExponential (t • x) (by simpa using hx.smul t) := by
  unfold nilpotentLieAdjointExponential nilpotentAdjointExponential
  rfl

private theorem nilpotentLieAdjointExponential_one
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    (x : L) (hx : IsNilpotent (ad K L x)) :
    nilpotentLieAdjointExponential x hx (1 : K) = nilpotentAdjointExponential x hx := by
  rw [nilpotentLieAdjointExponential_eq_scaled]
  congr 1
  exact one_smul K x

variable {K B : Type*} [Field K] [CharZero K]
  [CommRing B] [HopfAlgebra K B] [Algebra.FiniteType K B]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- The equality is

```lean
affineGroupAdjointRepresentation
      (gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) *
        gaAffineGroupPoints y (Multiplicative.ofAdd (-1 : K)) *
        gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K))) v = v - a • h
```
-/
theorem gaSl2PointProduct_adjoint_reflection
    (x y : B →ₐc[K] SymmetricAlgebra K K) (h v : 𝔤) (a : K)
    (hs : IsSl2Triple h (gaAffineGroupTangent x) (gaAffineGroupTangent y))
    (hvx : ⁅v, gaAffineGroupTangent x⁆ = a • gaAffineGroupTangent x)
    (hvy : ⁅v, gaAffineGroupTangent y⁆ = (-a) • gaAffineGroupTangent y) :
    affineGroupAdjointRepresentation
      (gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K)) *
        gaAffineGroupPoints y (Multiplicative.ofAdd (-1 : K)) *
        gaAffineGroupPoints x (Multiplicative.ofAdd (1 : K))) v = v - a • h := by
  have he := gaAffineGroupTangent_ad_nilpotent x
  have hf : IsNilpotent (ad K 𝔤 (-gaAffineGroupTangent y)) := by
    simpa using (gaAffineGroupTangent_ad_nilpotent y).neg
  simp only [map_mul, Module.End.mul_apply, affineGroupAdjointRepresentation_apply,
    gaAffineGroup_adjoint_eq_exponential]
  simp only [nilpotentLieAdjointExponential_one]
  simp only [nilpotentLieAdjointExponential_eq_scaled, neg_one_smul]
  exact
    sl2_adjoint_reflection h (gaAffineGroupTangent x) (gaAffineGroupTangent y)
      v a hs he hf hvx hvy

end ReductiveGroups
