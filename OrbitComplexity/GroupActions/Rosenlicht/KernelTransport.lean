import OrbitComplexity.GroupActions.Rosenlicht.PolynomialKernels

/-!
# Transport of polynomial relation kernels

Polynomial coefficient extension commutes with postcomposition and with
renaming variables. Algebra isomorphisms preserve the resulting kernels;
bijective renamings transport them by the inverse renaming.
-/

open MvPolynomial
open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u v w x y z

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {A : Type w} [CommRing A] [Algebra R A]
variable {B : Type x} [CommRing B] [Algebra R B]
variable {α : Type y} {β : Type z}

/-- The coefficient extension of a variable is its image in the right tensor
factor. -/
@[simp]
theorem polynomialTensorMap_X (f : MvPolynomial α R →ₐ[R] A) (i : α) :
    polynomialTensorMap S f (X i) = 1 ⊗ₜ[R] f (X i) := by
  simpa only [MvPolynomial.map_X] using polynomialTensorMap_map S f (X i)

/-- Polynomial coefficient extension commutes with postcomposition of algebra
maps. -/
theorem polynomialTensorMap_comp (f : MvPolynomial α R →ₐ[R] A) (g : A →ₐ[R] B) :
    polynomialTensorMap S (g.comp f) =
      (Algebra.TensorProduct.map (AlgHom.id S S) g).comp (polynomialTensorMap S f) := by
  ext i
  simp only [polynomialTensorMap_X, AlgHom.comp_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- Postcomposition by an algebra isomorphism does not change the kernel
of a coefficient-extended polynomial map. -/
theorem ker_polynomialTensorMap_algEquiv (f : MvPolynomial α R →ₐ[R] A)
    (e : A ≃ₐ[R] B) :
    RingHom.ker (polynomialTensorMap S (e.toAlgHom.comp f)) =
      RingHom.ker (polynomialTensorMap S f) := by
  rw [polynomialTensorMap_comp]
  apply RingHom.ker_comp_of_injective
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e).injective

/-- Polynomial coefficient extension commutes with bijective variable renaming. -/
theorem polynomialTensorMap_rename (f : MvPolynomial β R →ₐ[R] A) (e : α ≃ β) :
    polynomialTensorMap S (f.comp (MvPolynomial.renameEquiv R e).toAlgHom) =
      (polynomialTensorMap S f).comp (MvPolynomial.renameEquiv S e).toAlgHom := by
  ext i
  simp only [polynomialTensorMap_X, AlgHom.comp_apply]
  change 1 ⊗ₜ[R] f (MvPolynomial.rename e (X i)) =
    polynomialTensorMap S f (MvPolynomial.rename e (X i))
  simp only [MvPolynomial.rename_X, polynomialTensorMap_X]

omit [CommRing S] [Algebra R S] in
/-- Precomposition with a bijective renaming transports a polynomial relation
ideal by the inverse renaming. -/
theorem ker_comp_renameEquiv (f : MvPolynomial β R →ₐ[R] A) (e : α ≃ β) :
    RingHom.ker (f.comp (MvPolynomial.renameEquiv R e).toAlgHom) =
      (RingHom.ker f).map (MvPolynomial.renameEquiv R e.symm).toRingHom := by
  change RingHom.ker (f.toRingHom.comp (MvPolynomial.renameEquiv R e).toRingHom) = _
  rw [← RingHom.comap_ker]
  exact Ideal.comap_symm (MvPolynomial.renameEquiv R e).toRingEquiv.symm

/-- The kernel of a coefficient-extended map transforms under variable renaming
by the inverse renaming over the new coefficient algebra. -/
theorem ker_polynomialTensorMap_rename (f : MvPolynomial β R →ₐ[R] A) (e : α ≃ β) :
    RingHom.ker (polynomialTensorMap S
      (f.comp (MvPolynomial.renameEquiv R e).toAlgHom)) =
      (RingHom.ker (polynomialTensorMap S f)).map
        (MvPolynomial.renameEquiv S e.symm).toRingHom := by
  rw [polynomialTensorMap_rename, ker_comp_renameEquiv]

end

end GroupActions
