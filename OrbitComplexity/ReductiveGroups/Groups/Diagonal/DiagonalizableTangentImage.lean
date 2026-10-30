import OrbitComplexity.ReductiveGroups.Groups.Tangents.CharacterDifferential
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map
import Mathlib.Algebra.Lie.Nilpotent

/-!
# Diagonalizable Tangent Image

The image of a diagonalizable subgroup's tangent map, and its
character differentials.  -/

noncomputable section
namespace ReductiveGroups

variable {K B M : Type*} [Field K] [CommRing B] [HopfAlgebra K B] [CommGroup M]

/-- The Lie subalgebra given by the differential of a diagonalizable
group morphism. -/
def diagonalizableTangentImage (π : B →ₐc[K] MonoidAlgebra K M) :
    LieSubalgebra K (Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :=
  (TauCeti.derivationCompLieHom (B := K) π).range

/-- The tangent image of a diagonalizable group is an abelian Lie algebra. -/
instance diagonalizableTangentImage_isLieAbelian (π : B →ₐc[K] MonoidAlgebra K M) :
    IsLieAbelian (diagonalizableTangentImage π) := by
  apply (TauCeti.derivationCompLieHom (B := K) π).surjective_rangeRestrict.isLieAbelian
  exact ⟨diagonalizableTangent_lie_eq_zero⟩

/-- A closed diagonalizable subgroup has the same tangent algebra as its
image inside the original group's tangent algebra. -/
def diagonalizableTangentEquivImage (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) :
    Derivation K (MonoidAlgebra K M)
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K) ≃ₗ⁅K⁆
        diagonalizableTangentImage π :=
  (TauCeti.derivationCompLieHom (B := K) π).equivRangeOfInjective
    (TauCeti.derivationCompLieHom_injective_of_surjective π hπ)

/-- The equality is

```lean
(diagonalizableTangentEquivImage π hπ h :
      Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) =
        TauCeti.derivationComp (B := K) π h
```
-/
@[simp] theorem diagonalizableTangentEquivImage_coe
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π)
    (h : Derivation K (MonoidAlgebra K M)
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K)) :
    (diagonalizableTangentEquivImage π hπ h :
      Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) =
        TauCeti.derivationComp (B := K) π h := rfl

/-- The differential of the same character on the embedded tangent image. -/
def characterDifferentialOnImage (π : B →ₐc[K] MonoidAlgebra K M)
    (hπ : Function.Surjective π) (α : M) : diagonalizableTangentImage π →ₗ[K] K :=
  (characterDifferential α).comp
    (diagonalizableTangentEquivImage π hπ).symm.toLinearEquiv.toLinearMap

/-- The equality is

```lean
characterDifferentialOnImage π hπ α (diagonalizableTangentEquivImage π hπ h) =
      characterDifferential α h
```
-/
@[simp] theorem characterDifferentialOnImage_apply_equiv
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) (α : M)
    (h : Derivation K (MonoidAlgebra K M)
      (TauCeti.Bialgebra.CounitAlgebra K (MonoidAlgebra K M) K)) :
    characterDifferentialOnImage π hπ α (diagonalizableTangentEquivImage π hπ h) =
      characterDifferential α h := by
  change characterDifferential α
    ((diagonalizableTangentEquivImage π hπ).symm
      (diagonalizableTangentEquivImage π hπ h)) = characterDifferential α h
  rw [LieEquiv.symm_apply_apply]

/-- For these parameters,

```lean
characterDifferentialOnImage π hπ α ≠ 0
```
-/
theorem characterDifferentialOnImage_ne_zero
    (π : B →ₐc[K] MonoidAlgebra K M) (hπ : Function.Surjective π) (α : M)
    (hα : characterDifferential (K := K) α ≠ 0) :
    characterDifferentialOnImage π hπ α ≠ 0 := by
  intro hz
  apply hα
  ext h
  have hh := LinearMap.congr_fun hz (diagonalizableTangentEquivImage π hπ h)
  simpa only [characterDifferentialOnImage_apply_equiv, LinearMap.zero_apply] using hh

end ReductiveGroups
