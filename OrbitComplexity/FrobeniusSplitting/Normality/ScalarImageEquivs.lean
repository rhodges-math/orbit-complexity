import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.ScalarImages

/-!
# ScalarImageEquivs

Arithmetic coefficient models and compatible chart comparisons.
-/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {S R K M N A B : Type*}
    [CommRing S] [CommRing R] [CommRing K] [CommRing M] [CommRing N]
    [CommRing A] [CommRing B]
    [Algebra S R] [Algebra R K] [Algebra S K] [IsScalarTower S R K]
    [Algebra S M] [Algebra S N] [Algebra K A] [Algebra K B]
    [Algebra R A] [Algebra R B] [IsScalarTower R K A] [IsScalarTower R K B]
    (e : K ⊗[S] M ≃ₐ[K] A) (d : K ⊗[S] N ≃ₐ[K] B)
    (a : M ≃ₐ[S] N) (b : A ≃ₐ[K] B)
    (h : b.toAlgHom.comp e.toAlgHom =
      d.toAlgHom.comp (Algebra.TensorProduct.lTensor (S := K) K a.toAlgHom))

include a h

/-- Compatible changes of coefficient and generic coordinates identify their intrinsic
coefficient images. -/
theorem scalarImage_map_eq :
    (scalarImageHom (R := R) e).range.map (b.restrictScalars R).toAlgHom =
      (scalarImageHom (R := R) d).range := by
  let p : R ⊗[S] M →ₐ[R] R ⊗[S] N :=
    Algebra.TensorProduct.map (AlgHom.id R R) a.toAlgHom
  have hp : Function.Surjective p :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id a.surjective
  have heq : (b.restrictScalars R).toAlgHom.comp (scalarImageHom (R := R) e) =
      (scalarImageHom (R := R) d).comp p := by
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r m => exact AlgHom.congr_fun h (algebraMap R K r ⊗ₜ[S] m)
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  rw [← AlgHom.range_comp, heq, AlgHom.range_comp,
    (AlgHom.range_eq_top p).mpr hp, Algebra.map_top]

/-- Coordinate changes restrict to an equivalence between intrinsic coefficient images. -/
noncomputable def scalarImageEquiv :
    (scalarImageHom (R := R) e).range ≃ₐ[R] (scalarImageHom (R := R) d).range :=
  ((b.restrictScalars R).subalgebraMap (scalarImageHom (R := R) e).range).trans
    (Subalgebra.equivOfEq _ _ (scalarImage_map_eq e d a b h))

/-- The intrinsic-image equivalence evaluates as the generic coordinate change. -/
theorem scalarImageEquiv_apply (x : (scalarImageHom (R := R) e).range) :
    (scalarImageEquiv e d a b h x : B) = b x.val := rfl

end FrobeniusSplitting
