import OrbitComplexity.GroupActions.Rosenlicht.SplitKernels
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Flat.Basic

/-!
# Kernels under polynomial coefficient extension

A polynomial algebra map whose image is complemented as a module acquires no
new relations after coefficient extension: its new kernel is the extended
old kernel. The proof uses tensor right exactness and the polynomial tensor
isomorphism.
-/

open MvPolynomial
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w z

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {A : Type w} [CommRing A] [Algebra R A] {σ : Type z}

/-- The coefficient extension of a polynomial algebra map, with codomain the
scalar extension of its original codomain. -/
def polynomialTensorMap (f : MvPolynomial σ R →ₐ[R] A) :
    MvPolynomial σ S →ₐ[S] S ⊗[R] A :=
  (Algebra.TensorProduct.map (AlgHom.id S S) f).comp
    (MvPolynomial.algebraTensorAlgEquiv R S).symm.toAlgHom

/-- The scalar-extended polynomial map agrees with the original map on
polynomials whose coefficients come from the base ring. -/
theorem polynomialTensorMap_map (f : MvPolynomial σ R →ₐ[R] A)
    (p : MvPolynomial σ R) :
    polynomialTensorMap S f (MvPolynomial.map (algebraMap R S) p) = 1 ⊗ₜ[R] f p := by
  change (Algebra.TensorProduct.map (AlgHom.id S S) f)
    ((MvPolynomial.algebraTensorAlgEquiv R S).symm
      (MvPolynomial.map (algebraMap R S) p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_map]
  rfl

/-- The polynomial scalar extension is the tensor extension of its underlying
linear map under the polynomial tensor isomorphism. -/
theorem polynomialTensorMap_tensor (f : MvPolynomial σ R →ₐ[R] A)
    (t : S ⊗[R] MvPolynomial σ R) :
    polynomialTensorMap S f (MvPolynomial.algebraTensorAlgEquiv R S t) =
      f.toLinearMap.lTensor S t := by
  change (Algebra.TensorProduct.map (AlgHom.id S S) f)
    ((MvPolynomial.algebraTensorAlgEquiv R S).symm
      (MvPolynomial.algebraTensorAlgEquiv R S t)) = _
  rw [AlgEquiv.symm_apply_apply]
  induction t using TensorProduct.inductionOn with
  | tmul s p => rfl
  | add t q ht hq => simp only [map_add, ht, hq]

private lemma ker_polynomialTensorMap_of_exact (f : MvPolynomial σ R →ₐ[R] A)
    (hexact : Function.Exact ((LinearMap.ker f.toLinearMap).subtype.lTensor S)
      (f.toLinearMap.lTensor S)) :
    RingHom.ker (polynomialTensorMap S f) =
      (RingHom.ker f).map (MvPolynomial.map (algebraMap R S)) := by
  let I := RingHom.ker f
  let J := I.map (MvPolynomial.map (algebraMap R S))
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) R S
  have hle : J ≤ RingHom.ker (polynomialTensorMap S f) := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change polynomialTensorMap S f (MvPolynomial.map (algebraMap R S) p) = 0
    rw [polynomialTensorMap_map, show f p = 0 from hp, TensorProduct.tmul_zero]
  apply le_antisymm ?_ hle
  intro p hp
  have ht : e.symm p ∈ LinearMap.ker (f.toLinearMap.lTensor S) := by
    change f.toLinearMap.lTensor S (e.symm p) = 0
    rw [← polynomialTensorMap_tensor, e.apply_symm_apply]
    exact hp
  rw [LinearMap.exact_iff.mp hexact] at ht
  obtain ⟨t, ht⟩ := ht
  have himage (z : S ⊗[R] LinearMap.ker f.toLinearMap) :
      e ((LinearMap.ker f.toLinearMap).subtype.lTensor S z) ∈ J := by
    induction z using TensorProduct.inductionOn with
    | tmul s q =>
      change e (s ⊗ₜ[R] q.val) ∈ J
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
      exact (J.restrictScalars S).smul_mem s (Ideal.mem_map_of_mem _ q.property)
    | add t q ht hq =>
      simp only [map_add]
      exact J.add_mem ht hq
  have he : e ((LinearMap.ker f.toLinearMap).subtype.lTensor S t) = p :=
    (congrArg e ht).trans (e.apply_symm_apply p)
  rw [← he]
  exact himage t

/-- A complemented polynomial image has its full relation ideal preserved by
every coefficient extension. -/
theorem ker_polynomialTensorMap (f : MvPolynomial σ R →ₐ[R] A)
    (C : Submodule R A) (hC : IsCompl (LinearMap.range f.toLinearMap) C) :
    RingHom.ker (polynomialTensorMap S f) =
      (RingHom.ker f).map (MvPolynomial.map (algebraMap R S)) :=
  ker_polynomialTensorMap_of_exact S f (LinearMap.exact_iff.mpr
    (ker_lTensor_of_isCompl_range f.toLinearMap C hC S))

/-- A flat coefficient extension preserves the relation ideal of every
polynomial algebra map. -/
theorem ker_polynomialTensorMap_of_flat [Module.Flat R S]
    (f : MvPolynomial σ R →ₐ[R] A) :
    RingHom.ker (polynomialTensorMap S f) =
      (RingHom.ker f).map (MvPolynomial.map (algebraMap R S)) :=
  ker_polynomialTensorMap_of_exact S f
    (Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map f.toLinearMap))

end

end GroupActions
