import OrbitComplexity.FrobeniusSplitting.Splittings.TensorProduct
import OrbitComplexity.FrobeniusSplitting.Splittings.LinearMap
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.CharP.Algebra

/-! # Tensor products of Frobenius-linear operators

The inverse-Frobenius semilinear tensor construction does not require either
factor operator to take one to one.
-/

noncomputable section

namespace FrobeniusSplitting.FrobeniusLinearMap

open scoped TensorProduct

variable {K S T : Type*} {p : ℕ}

section Semilinear

variable [CommSemiring K] [ExpChar K p] [PerfectRing K p]
    [CommSemiring S] [Algebra K S]

private def toSemilinear (splitting : FrobeniusLinearMap S p) :
    S →ₛₗ[(frobeniusEquiv K p).symm.toRingHom] S where
  toFun := fun a ↦ splitting a
  map_add' := splitting.map_add
  map_smul' r a := by
    simp only [Algebra.smul_def]
    change splitting (algebraMap K S r * a) =
      algebraMap K S ((frobeniusEquiv K p).symm r) * splitting a
    have hr : algebraMap K S ((frobeniusEquiv K p).symm r) ^ p = algebraMap K S r := by
      rw [← _root_.map_pow]
      exact congrArg (algebraMap K S) ((frobeniusEquiv K p).apply_symm_apply r)
    rw [← hr, splitting.map_pow_mul]

end Semilinear

section TensorProduct

variable [Field K] [ExpChar K p] [PerfectRing K p]
    [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]

private def tensorMap (left : FrobeniusLinearMap S p) (right : FrobeniusLinearMap T p) :
    S ⊗[K] T →ₛₗ[(frobeniusEquiv K p).symm.toRingHom] S ⊗[K] T :=
  TensorProduct.map left.toSemilinear right.toSemilinear

private theorem tensorMap_pow_mul (left : FrobeniusLinearMap S p) (right : FrobeniusLinearMap T p)
    (a b : S ⊗[K] T) : tensorMap left right (a ^ p * b) = a * tensorMap left right b := by
  by_cases h : Subsingleton (S ⊗[K] T)
  · exact @Subsingleton.elim _ h _ _
  have : Nontrivial (S ⊗[K] T) := not_subsingleton_iff_nontrivial.mp h
  have : ExpChar (S ⊗[K] T) p := expChar_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective K (S ⊗[K] T)) p
  induction a using TensorProduct.inductionOn with
  | tmul a c =>
    induction b using TensorProduct.inductionOn with
    | tmul b d =>
      change tensorMap left right ((a ⊗ₜ[K] c) ^ p * (b ⊗ₜ[K] d)) =
        (a ⊗ₜ[K] c) * tensorMap left right (b ⊗ₜ[K] d)
      rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
      change left (a ^ p * b) ⊗ₜ[K] right (c ^ p * d) =
        (a ⊗ₜ[K] c) * (left b ⊗ₜ[K] right d)
      rw [left.map_pow_mul, right.map_pow_mul, Algebra.TensorProduct.tmul_mul_tmul]
    | add b d hb hd =>
      rw [mul_add, (tensorMap left right).map_add, hb, hd,
        (tensorMap left right).map_add, mul_add]
  | add a c ha hc =>
    rw [add_pow_expChar, add_mul, (tensorMap left right).map_add, ha, hc, add_mul]

/-- Frobenius-linear operators over a perfect field tensor without normalization. -/
def tensorProduct (left : FrobeniusLinearMap S p) (right : FrobeniusLinearMap T p) :
    FrobeniusLinearMap (S ⊗[K] T) p where
  toAddMonoidHom := (tensorMap left right).toAddMonoidHom
  map_pow_mul' := tensorMap_pow_mul left right

/-- The tensor product operator applies its factors to each pure tensor. -/
theorem tensorProduct_tmul (left : FrobeniusLinearMap S p) (right : FrobeniusLinearMap T p)
    (a : S) (b : T) :
    tensorProduct (K := K) left right (a ⊗ₜ[K] b) = left a ⊗ₜ[K] right b := rfl

variable {S' T' : Type*} [CommRing S'] [CommRing T'] [Algebra K S'] [Algebra K T']

/-- Algebra maps commuting with the factor operators commute with the tensor operator. -/
theorem tensorProduct_naturality (left : FrobeniusLinearMap S p) (right : FrobeniusLinearMap T p)
    (left' : FrobeniusLinearMap S' p) (right' : FrobeniusLinearMap T' p)
    (f : S →ₐ[K] S') (g : T →ₐ[K] T')
    (hf : ∀ a, left' (f a) = f (left a)) (hg : ∀ b, right' (g b) = g (right b))
    (a : S ⊗[K] T) :
    tensorProduct left' right' (Algebra.TensorProduct.map f g a) =
      Algebra.TensorProduct.map f g (tensorProduct left right a) := by
  induction a using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, tensorProduct_tmul,
      tensorProduct_tmul, Algebra.TensorProduct.map_tmul, hf, hg]
  | add a b ha hb =>
    simp only [_root_.map_add, ha, hb]

end TensorProduct

end FrobeniusSplitting.FrobeniusLinearMap
