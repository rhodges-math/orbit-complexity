import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import Mathlib.Algebra.Group.Units.Hom

/-!
# Point Convolution Units

Affine-group points embed as units of the convolution algebra
of linear maps. This transfers group commutator words to ring calculations. -/

noncomputable section
namespace ReductiveGroups

open WithConv

variable {K B A : Type*} [Field K] [CommRing B] [HopfAlgebra K B]
  [CommRing A] [Algebra K A]

/-- The monoid homomorphism regarding a point `B →ₐ[K] A` of the affine group as a linear map `B
→ₗ[K] A`, with both sides under convolution. -/
def pointConvolutionLinear :
    WithConv (B →ₐ[K] A) →* WithConv (B →ₗ[K] A) where
  toFun p := toConv p.ofConv.toLinearMap
  map_one' := AlgHom.toLinearMap_convOne
  map_mul' p q := AlgHom.toLinearMap_convMul p q

/-- The monoid homomorphism sending a point `B →ₐ[K] A` of the affine group to the corresponding
unit of the convolution algebra of linear maps `B →ₗ[K] A`. -/
def pointConvolutionUnits :
    WithConv (B →ₐ[K] A) →* (WithConv (B →ₗ[K] A))ˣ :=
  (pointConvolutionLinear (K := K) (B := B) (A := A)).toHomUnits

/-- The equality is

```lean
((pointConvolutionUnits (K := K) (B := B) (A := A) p :
      (WithConv (B →ₗ[K] A))ˣ) : WithConv (B →ₗ[K] A)) =
        toConv p.ofConv.toLinearMap
```
-/
@[simp] theorem pointConvolutionUnits_val (p : WithConv (B →ₐ[K] A)) :
    ((pointConvolutionUnits (K := K) (B := B) (A := A) p :
      (WithConv (B →ₗ[K] A))ˣ) : WithConv (B →ₗ[K] A)) =
        toConv p.ofConv.toLinearMap := rfl

end ReductiveGroups
