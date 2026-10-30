import OrbitComplexity.FrobeniusSplitting.Splittings.Perfect
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.CharP.Algebra

/-!
# Tensor products of Frobenius splittings

Over a perfect field, every splitting is semilinear for inverse Frobenius on
scalars. Tensoring these semilinear maps defines a splitting of a tensor product
of commutative algebras, including the zero tensor product.

## Main definitions

* `FrobeniusSplitting.RingSplitting.toSemilinear`: inverse-Frobenius semilinearity.
* `FrobeniusSplitting.RingSplitting.tensorProduct`: the tensor product splitting.

## Main results

* `FrobeniusSplitting.RingSplitting.tensorProduct_tmul`: the formula on pure tensors.
* `FrobeniusSplitting.RingSplitting.tensorProduct_naturality`: naturality of tensoring.
-/

noncomputable section

namespace FrobeniusSplitting.RingSplitting

open scoped TensorProduct

variable {K S T : Type*} {p : ℕ}

section Semilinear

variable [CommSemiring K] [ExpChar K p] [PerfectRing K p]
    [CommSemiring S] [Algebra K S]

/-- A splitting over a perfect ring is semilinear for inverse Frobenius. -/
def toSemilinear (splitting : RingSplitting S p) :
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

private def tensorMap (left : RingSplitting S p) (right : RingSplitting T p) :
    S ⊗[K] T →ₛₗ[(frobeniusEquiv K p).symm.toRingHom] S ⊗[K] T :=
  TensorProduct.map left.toSemilinear right.toSemilinear

private theorem tensorMap_pow_mul (left : RingSplitting S p) (right : RingSplitting T p)
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

/-- Splittings of algebras over a perfect field give a splitting of their tensor product. -/
def tensorProduct (left : RingSplitting S p) (right : RingSplitting T p) :
    RingSplitting (S ⊗[K] T) p where
  toAddMonoidHom := (tensorMap left right).toAddMonoidHom
  map_pow_mul' := tensorMap_pow_mul left right
  map_one' := by
    change tensorMap left right (1 : S ⊗[K] T) = 1
    rw [Algebra.TensorProduct.one_def]
    change left 1 ⊗ₜ[K] right 1 = (1 : S ⊗[K] T)
    rw [left.map_one, right.map_one, Algebra.TensorProduct.one_def]

variable {S' T' : Type*} [CommRing S'] [CommRing T'] [Algebra K S'] [Algebra K T']

end TensorProduct

end FrobeniusSplitting.RingSplitting
