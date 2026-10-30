import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Scalar extension of maps with complemented image

A complemented image stays embedded after tensoring, because its projection
provides a left inverse. Right exactness then identifies the new kernel with
the image of the scalar extension of the original kernel.
-/

open LinearMap

namespace GroupActions

universe u v w z

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {Q : Type w} [AddCommGroup Q] [Module R Q]

/-- Tensoring preserves the kernel of a linear map whose image has a complement. -/
theorem ker_lTensor_of_isCompl_range (f : P →ₗ[R] Q) (C : Submodule R Q)
    (hC : IsCompl (LinearMap.range f) C) (S : Type z) [AddCommGroup S] [Module R S] :
    LinearMap.ker (f.lTensor S) =
      LinearMap.range ((LinearMap.ker f).subtype.lTensor S) := by
  let i := (LinearMap.range f).subtype
  let π := (LinearMap.range f).projectionOnto C hC
  have hπ : π.comp i = LinearMap.id := Submodule.projectionOnto_comp_subtype hC
  have hi : Function.Injective (i.lTensor S) := by
    apply Function.HasLeftInverse.injective
    refine ⟨π.lTensor S, ?_⟩
    intro x
    have he := congrArg (fun g : (LinearMap.range f) →ₗ[R] LinearMap.range f ↦
      g.lTensor S x) hπ
    simpa only [LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.lTensor_id,
      LinearMap.id_apply] using he
  have hcomp : f.lTensor S = (i.lTensor S).comp (f.rangeRestrict.lTensor S) := by
    ext a p
    rfl
  rw [hcomp, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hi)]
  have he := lTensor_exact S (LinearMap.exact_subtype_ker_map f.rangeRestrict)
    (LinearMap.surjective_rangeRestrict f)
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict] at he
  exact he

end GroupActions
