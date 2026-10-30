import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent

/-!
# Affine Group Matrix Differential

The differential of a coordinate representation of an affine group in `GLₙ`. -/

noncomputable section
namespace ReductiveGroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K B : Type*} [Field K] [CommRing B] [Bialgebra K B]

/-- The tangent Lie map of a coordinate bialgebra representation. -/
def affineGroupMatrixDifferential (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B) :
    Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K) →ₗ⁅K⁆
      Matrix (Fin n) (Fin n) K :=
  (TauCeti.GeneralLinear.tangentLieEquivMatrix (R := K) (B := K) n).toLieHom.comp
    (TauCeti.derivationCompLieHom (B := K) ρ)

/-- The equality is

```lean
affineGroupMatrixDifferential n ρ d =
      TauCeti.GeneralLinear.tangentMatrix n (TauCeti.derivationComp (B := K) ρ d)
```
-/
@[simp] theorem affineGroupMatrixDifferential_apply (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (d : Derivation K B (TauCeti.Bialgebra.CounitAlgebra K B K)) :
    affineGroupMatrixDifferential n ρ d =
      TauCeti.GeneralLinear.tangentMatrix n (TauCeti.derivationComp (B := K) ρ d) := by
  simp [affineGroupMatrixDifferential]

/-- A surjective coordinate map has injective differential. -/
theorem AffineGroupMatrixDifferential.injective_of_surjective (n : ℕ)
    (ρ : TauCeti.GeneralLinear.coordinateHopfAlgebra K n →ₐc[K] B)
    (hρ : Function.Surjective ρ) :
    Function.Injective (affineGroupMatrixDifferential n ρ) := by
  intro d e h
  apply TauCeti.derivationCompLieHom_injective_of_surjective (B := K) ρ hρ
  exact (TauCeti.GeneralLinear.tangentLieEquivMatrix (R := K) (B := K) n).injective
    (by simpa [affineGroupMatrixDifferential] using h)

end ReductiveGroups
