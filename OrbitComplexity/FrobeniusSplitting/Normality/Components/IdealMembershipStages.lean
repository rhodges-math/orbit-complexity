import OrbitComplexity.FrobeniusSplitting.Normality.Models.FiniteRelations
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Batteries.Tactic.Lint

/-! # Retaining ideal membership on prescribed algebra models

A finite family of ideal-membership relations can be retained by killing
the corresponding quotient classes after a coefficient enlargement.
The original algebras and ideals are extended by tensors throughout.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace FrobeniusSplitting

universe u v w

private theorem tensor_quotient_zero_iff
    {S R A : Type*} [CommRing S] [CommRing R] [CommRing A]
    [Algebra S R] [Algebra S A] (I : Ideal A) (x : A) :
    (1 : R) ⊗ₜ[S] Ideal.Quotient.mk I x = 0 ↔
      (1 : R) ⊗ₜ[S] x ∈
        I.map (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom := by
  have hk0 :
      RingHom.ker
          (Algebra.TensorProduct.lTensor (S := R) R (Ideal.Quotient.mkₐ S I)).toRingHom =
        (RingHom.ker (Ideal.Quotient.mkₐ S I).toRingHom).map
          (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom :=
    Algebra.TensorProduct.lTensor_ker (A := R)
      (g := Ideal.Quotient.mkₐ S I) (Ideal.Quotient.mkₐ_surjective S I)
  have hq : RingHom.ker (Ideal.Quotient.mkₐ S I).toRingHom = I := Ideal.mk_ker
  have hk := hk0.trans (congrArg (fun P : Ideal A =>
    P.map (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom) hq)
  rw [← hk]
  rfl

/-- Finitely many ideal-membership relations valid over the original field
hold on tensor extensions of the same algebras and ideals after one
finitely generated coefficient enlargement. -/
theorem exists_retained_ideal_membership
    {K : Type u} [hK : Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type v} [hJ : Finite J] (A : J → Type w)
    [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (I : ∀ j, Ideal (A j)) (x : ∀ j, A j)
    (hx : ∀ j, (1 : K) ⊗ₜ[S] x j ∈
      (I j).map (Algebra.TensorProduct.includeRight : A j →ₐ[S] K ⊗[S] A j).toRingHom) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T),
      letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
      letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
      T.FG ∧ ∀ j, (1 : T) ⊗ₜ[S] x j ∈
        (I j).map
          (Algebra.TensorProduct.includeRight : A j →ₐ[S] T ⊗[S] A j).toRingHom := by
  have hzero : ∀ j, (1 : K) ⊗ₜ[S] Ideal.Quotient.mk (I j) (x j) = 0 :=
    fun j => (tensor_quotient_zero_iff (I j) (x j)).mpr (hx j)
  obtain ⟨T, hST, hT, hzeroT⟩ :=
    @exists_retained_zero_relations.{u, v, w} K hK S hS J hJ
      (fun j => A j ⧸ I j) (fun j => inferInstance) (fun j => inferInstance)
      (fun j => Ideal.Quotient.mk (I j) (x j)) hzero
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  refine ⟨T, hST, hT, ?_⟩
  intro j
  exact (tensor_quotient_zero_iff (I j) (x j)).mp (hzeroT j)

end FrobeniusSplitting
