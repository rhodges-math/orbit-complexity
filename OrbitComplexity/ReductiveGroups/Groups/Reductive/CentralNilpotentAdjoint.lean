import OrbitComplexity.ReductiveGroups.Lie.Cartan.CentralNilpotentIdeal
import OrbitComplexity.ReductiveGroups.Groups.Representations.AdjointRadicalCharacteristic
import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupAdjointMatrix

/-!
# Central Nilpotent Adjoint

The whole family of central matrix-nilpotent tangents is preserved by
every point adjoint of the original affine group. -/

noncomputable section
namespace ReductiveGroups

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

local notation "𝔤" => Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)

/-- For these parameters,

```lean
affineGroupAdjointRepresentation g d ∈ LieAlgebra.center K 𝔤
```
-/
theorem affineGroupAdjoint_mem_center (g : WithConv (B →ₐ[K] K))
    (d : 𝔤) (hd : d ∈ LieAlgebra.center K 𝔤) :
    affineGroupAdjointRepresentation g d ∈ LieAlgebra.center K 𝔤 := by
  let e := affineGroupAdjointLieEquiv g
  change ∀ x : 𝔤, ⁅x, e d⁆ = 0
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  change ⁅e y, e d⁆ = 0
  rw [← e.map_lie, hd y, map_zero]

/-- Nilpotence is transported by the matrix of the same original group
point, using adjoint naturality. -/
theorem affineGroupAdjoint_matrix_nilpotent (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (g : WithConv (B →ₐ[K] K)) (d : 𝔤)
    (hd : IsNilpotent (affineGroupMatrixDifferential n ρ d)) :
    IsNilpotent (affineGroupMatrixDifferential n ρ (affineGroupAdjointRepresentation g d)) := by
  rw [affineGroupAdjointRepresentation_apply, affineGroupMatrixDifferential_adjoint]
  obtain ⟨r, hr⟩ := hd
  refine ⟨r, ?_⟩
  rw [Units.conj_pow, hr, mul_zero, zero_mul]

/-- The exact central-nilpotent ideal, for the fixed coordinate
representation, is invariant under all original point adjoints. -/
theorem affineGroupAdjoint_centralNilpotentIdeal (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (g : WithConv (B →ₐ[K] K)) (d : 𝔤)
    (hd : d ∈ centralNilpotentIdeal (affineGroupMatrixDifferential n ρ)) :
    affineGroupAdjointRepresentation g d ∈
      centralNilpotentIdeal (affineGroupMatrixDifferential n ρ) :=
  ⟨affineGroupAdjoint_mem_center g d hd.1,
    affineGroupAdjoint_matrix_nilpotent n ρ g d hd.2⟩

end ReductiveGroups
