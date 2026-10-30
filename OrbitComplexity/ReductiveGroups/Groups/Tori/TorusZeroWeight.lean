import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterLieWeightComparison
import Mathlib.Algebra.Lie.Weights.Cartan

/-!
# Torus Zero Weight

The zero character weight is the ordinary centralizer of the torus
tangent image. Equality with that image is the Cartan property
`reductive_maximalTorus_coordinateTangent_isCartan`
(`Groups/MaximalTorusLieCartan.lean`). -/

noncomputable section
namespace ReductiveGroups

universe u
variable {K B ι : Type u} [Field K] [CharZero K] [CommRing B]
  [HopfAlgebra K B] [Algebra.FiniteType K B]

omit [CharZero K] [Algebra.FiniteType K B] in
/-- The equality is

```lean
characterDifferentialOnImage π hπ 1 = 0
```
-/
@[simp] theorem characterDifferentialOnImage_one
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) :
    characterDifferentialOnImage π hπ 1 = 0 := by
  ext x
  obtain ⟨h, rfl⟩ := (diagonalizableTangentEquivImage π hπ).surjective x
  change characterDifferentialOnImage π hπ 1
    (diagonalizableTangentEquivImage π hπ h) = 0
  rw [characterDifferentialOnImage_apply_equiv, characterDifferential_one,
    LinearMap.zero_apply]

/-- The trivial-character submodule is the zero generalized Lie
root submodule of the same embedded torus tangent algebra. -/
theorem AffineGroupIdentityWeight.eq_rootSpace_zero
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) :
    affineGroupCharacterWeightSpace π 1 =
      (LieAlgebra.rootSpace (diagonalizableTangentImage π) 0).toSubmodule := by
  rw [AffineGroupCharacterWeightSpace.eq_rootSpace π hπ,
    characterDifferentialOnImage_one]
  rfl

/-- Trivial character weight is equivalent to commuting with every vector
in the torus tangent image; no reductivity is required. -/
theorem mem_affineGroupIdentityWeight_iff
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    d ∈ affineGroupCharacterWeightSpace π 1 ↔
      ∀ x : diagonalizableTangentImage π,
        ⁅(x : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)), d⁆ = 0 := by
  constructor
  · intro hd x
    obtain ⟨h, rfl⟩ := (diagonalizableTangentEquivImage π hπ).surjective x
    change ⁅(diagonalizableTangentEquivImage π hπ h :
      Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)), d⁆ = 0
    rw [diagonalizableTangentEquivImage_coe,
      bracket_eq_character_derivative π 1 h d hd]
    change characterDifferential (K := K) 1 h • d = 0
    rw [characterDifferential_one, LinearMap.zero_apply]
    exact zero_smul K d
  · intro hd
    rw [AffineGroupIdentityWeight.eq_rootSpace_zero π hπ]
    apply (LieModule.mem_genWeightSpace _ _ _).mpr
    intro x
    refine ⟨1, ?_⟩
    change ⁅(x : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)), d⁆ -
      (0 : K) • d = 0
    exact sub_eq_zero.mpr ((hd x).trans (zero_smul K d).symm)

/-- Cartan status is exactly the assertion that the trivial character
summand consists of tangent vectors of the torus itself. -/
theorem torusTangent_isCartan_iff_identityWeight
    (π : B →ₐc[K] MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (hπ : Function.Surjective π) :
    (diagonalizableTangentImage π).IsCartanSubalgebra ↔
      affineGroupCharacterWeightSpace π 1 =
        (diagonalizableTangentImage π).toSubmodule := by
  let := finiteTypeAffineGroup_tangent_finite (K := K) (B := B)
  rw [AffineGroupIdentityWeight.eq_rootSpace_zero π hπ]
  rw [← LieAlgebra.eq_rootSpace_zero_iff_isCartan]
  constructor
  · intro h
    rw [← h]
    rfl
  · intro h
    apply LieSubmodule.toSubmodule_injective
    exact h.symm

end ReductiveGroups
