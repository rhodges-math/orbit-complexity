import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Smoothness of pointed tensor factors

A point of one tensor factor retracts the tensor product onto the other factor.
The infinitesimal lifting property descends through this retraction.
-/

open scoped TensorProduct
namespace FrobeniusSplitting

private theorem formallySmooth_of_retract {R A W : Type*}
    [CommRing R] [CommRing A] [CommRing W] [Algebra R A] [Algebra R W]
    [Algebra.FormallySmooth R W] (i : A →ₐ[R] W) (r : W →ₐ[R] A)
    (h : r.comp i = AlgHom.id R A) : Algebra.FormallySmooth R A := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro Q _ _ I hI f
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective R W I hI (f.comp r)
  refine ⟨g.comp i, ?_⟩
  rw [← AlgHom.comp_assoc, hg, AlgHom.comp_assoc, h, AlgHom.comp_id]

/-- A finitely presented tensor factor is smooth when the total product is smooth
and the other factor has an algebra-valued base point. -/
theorem smooth_of_pointed_product (R A B : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.FinitePresentation R A] [Algebra.Smooth R (A ⊗[R] B)]
    (epsilon : B →ₐ[R] R) : Algebra.Smooth R A := by
  let i : A →ₐ[R] A ⊗[R] B :=
    (Algebra.TensorProduct.includeLeft : A →ₐ[A] A ⊗[R] B).restrictScalars R
  let r : A ⊗[R] B →ₐ[R] A := Algebra.TensorProduct.lift (AlgHom.id R A)
    ((Algebra.ofId R A).comp epsilon) (fun _ _ => Commute.all _ _)
  have h : r.comp i = AlgHom.id R A := by
    ext a
    change r (a ⊗ₜ[R] (1 : B)) = a
    simp only [r, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, map_one, mul_one]
  have : Algebra.FormallySmooth R A := formallySmooth_of_retract i r h
  exact ⟨inferInstance, inferInstance⟩

end FrobeniusSplitting
