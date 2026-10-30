import Batteries.Tactic.Lint
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic

/-!
# TensorCoefficients

Tensor and localization comparisons for coefficient models.
-/

open scoped TensorProduct

namespace FrobeniusSplitting


/-- Tensoring a subalgebra inclusion with a flat algebra preserves injectivity. -/
theorem tensor_subalgebra_injective {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] [Module.Flat S B] (M : Subalgebra S A) :
    Function.Injective (Algebra.TensorProduct.map M.val (AlgHom.id S B)) := by
  have heq : (Algebra.TensorProduct.map M.val (AlgHom.id S B)).toLinearMap =
      M.val.toLinearMap.rTensor B := by
    ext m b
    rfl
  change Function.Injective (Algebra.TensorProduct.map M.val (AlgHom.id S B)).toLinearMap
  rw [heq]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

end FrobeniusSplitting
