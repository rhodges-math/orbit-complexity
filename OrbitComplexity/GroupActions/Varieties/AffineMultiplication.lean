import OrbitComplexity.GroupActions.Varieties.AffineProduct
import Mathlib.RingTheory.Bialgebra.Convolution

/-! # Affine multiplication in coordinates

Comultiplication on a coordinate bialgebra defines multiplication after restriction to two
affine factors. Evaluation at a pair of points agrees with the convolution product.

## Main definitions

* `GroupActions.affineMulMap`: the coordinate homomorphism for restricted multiplication.

## Main results

* `GroupActions.affineMulMap_points`: evaluation agrees with convolution of the two included points.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u

variable {K H A B : Type u} [CommRing K] [CommRing H] [Bialgebra K H]
  [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- Restrict multiplication in an affine monoid to two affine coordinate maps. -/
def affineMulMap (f : H →ₐ[K] A) (g : H →ₐ[K] B) : H →ₐ[K] A ⊗[K] B :=
  (Algebra.TensorProduct.map f g).comp (Bialgebra.comulAlgHom K H)

/-- Evaluation of restricted multiplication is convolution of the two included points. -/
theorem affineMulMap_points (f : H →ₐ[K] A) (g : H →ₐ[K] B)
    (p : (A →ₐ[K] K) × (B →ₐ[K] K)) :
    ((tensorAlgebraPointsEquiv K A B).symm p).comp (affineMulMap f g) =
      ((WithConv.toConv (p.1.comp f)) * (WithConv.toConv (p.2.comp g))).ofConv := by
  rw [AlgHom.convMul_def]
  change (Algebra.TensorProduct.lift p.1 p.2 (fun _ _ => .all _ _)).comp
      ((Algebra.TensorProduct.map f g).comp (Bialgebra.comulAlgHom K H)) = _
  have ht : (Algebra.TensorProduct.lift p.1 p.2 (fun _ _ => .all _ _)).comp
      (Algebra.TensorProduct.map f g) =
      Algebra.TensorProduct.lift (p.1.comp f) (p.2.comp g) (fun _ _ => .all _ _) := by
    ext <;> simp
  change (Algebra.TensorProduct.lift p.1 p.2 (fun _ _ => .all _ _)).comp
      ((Algebra.TensorProduct.map f g).comp (Bialgebra.comulAlgHom K H)) =
    (Algebra.TensorProduct.lmul' K).comp
      ((Algebra.TensorProduct.map (p.1.comp f) (p.2.comp g)).comp
        (Bialgebra.comulAlgHom K H))
  rw [← AlgHom.comp_assoc, ht, ← AlgHom.comp_assoc, Algebra.TensorProduct.lmul'_comp_map]

end

end GroupActions
