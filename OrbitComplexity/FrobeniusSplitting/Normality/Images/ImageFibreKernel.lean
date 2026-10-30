import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.QuotientBaseChange
import OrbitComplexity.FrobeniusSplitting.Normality.Retractions.RetractionEnlargement

/-! The image ideal in every coefficient fibre of a split quotient factorization. -/

open scoped TensorProduct

namespace FrobeniusSplitting

variable {R F A B : Type*} [CommRing R] [CommRing F] [CommRing A] [CommRing B]
    [Algebra R F] [Algebra R A] [Algebra R B]

private theorem tensor_quotient_kernel (I : Ideal A) :
    RingHom.ker (Algebra.TensorProduct.lTensor (S := F) F
      (Ideal.Quotient.mkₐ R I)).toRingHom =
        I.map (Algebra.TensorProduct.includeRight : A →ₐ[R] F ⊗[R] A).toRingHom := by
  let J : Ideal (F ⊗[R] A) :=
    I.map (Algebra.TensorProduct.includeRight : A →ₐ[R] F ⊗[R] A).toRingHom
  let q := Algebra.TensorProduct.lTensor (S := F) F (Ideal.Quotient.mkₐ R I)
  let e : F ⊗[R] (A ⧸ I) ≃ₐ[F] (F ⊗[R] A) ⧸ J :=
    Algebra.TensorProduct.tensorQuotientEquiv F A F I
  have he : (e.toAlgHom.comp q).toRingHom = Ideal.Quotient.mk J := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  calc
    RingHom.ker q.toRingHom = RingHom.ker
        ((e : _ →+* _).comp q.toRingHom) :=
      (RingHom.ker_comp_of_injective q.toRingHom e.injective).symm
    _ = J := by
      change RingHom.ker (e.toAlgHom.comp q).toRingHom = J
      rw [he]
      exact Ideal.mk_ker

/-- A split image factorization retains its exact image ideal after any coefficient extension. -/
theorem image_fibre_kernel (I : Ideal A) (f : A ⧸ I →ₐ[R] B)
    (r : B →ₗ[R] A ⧸ I) (hr : r.comp f.toLinearMap = LinearMap.id) :
    RingHom.ker ((Algebra.TensorProduct.lTensor (S := F) F f).comp
      (Algebra.TensorProduct.lTensor (S := F) F (Ideal.Quotient.mkₐ R I))).toRingHom =
        I.map (Algebra.TensorProduct.includeRight : A →ₐ[R] F ⊗[R] A).toRingHom := by
  have hrF : (r.baseChange F).comp (f.toLinearMap.baseChange F) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
  have hi : Function.Injective (Algebra.TensorProduct.lTensor (S := F) F f) := by
    exact (show Function.LeftInverse (r.baseChange F)
      (Algebra.TensorProduct.lTensor (S := F) F f) from
        fun x => LinearMap.congr_fun hrF x).injective
  change RingHom.ker ((Algebra.TensorProduct.lTensor (S := F) F f).toRingHom.comp
    (Algebra.TensorProduct.lTensor (S := F) F (Ideal.Quotient.mkₐ R I)).toRingHom) = _
  rw [RingHom.ker_comp_of_injective _ hi]
  exact tensor_quotient_kernel I

end FrobeniusSplitting
