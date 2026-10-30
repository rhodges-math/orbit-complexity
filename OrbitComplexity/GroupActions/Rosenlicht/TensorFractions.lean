import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Fraction fields after tensor localization

Localizing one coordinate algebra to its fraction field does not change the
fraction field of a tensor product. This identifies the rational functions on
an integral affine product with the rational functions after passage to the
generic point of its first factor.

## Main definitions

* `tensorFractionEquiv`: the fraction-field comparison after tensor localization.
-/

namespace GroupActions

noncomputable section

open scoped TensorProduct

universe u v w z

variable (K : Type u) [Field K]
variable (A : Type v) [CommRing A] [Algebra K A]
variable (F : Type w) [Field F] [Algebra K F] [Algebra A F]
variable [IsScalarTower K A F] [IsFractionRing A F]
variable (B : Type z) [CommRing B] [Algebra K B]
variable [IsDomain (A ⊗[K] B)]

private def tensorFractionMap : A ⊗[K] B →ₐ[K] F ⊗[K] B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A F) (AlgHom.id K B)

private def tensorToFraction : F ⊗[K] B →ₐ[K] FractionRing (A ⊗[K] B) := by
  have : Nontrivial B :=
    (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom.domain_nontrivial
  exact Algebra.TensorProduct.lift
    (IsFractionRing.liftAlgHom (K := F)
      (g := (IsScalarTower.toAlgHom K (A ⊗[K] B) (FractionRing (A ⊗[K] B))).comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B))
      ((IsFractionRing.injective (A ⊗[K] B) _).comp
        (Algebra.TensorProduct.includeLeft_injective (R := K) (S := K) (A := A) (B := B)
          (algebraMap K B).injective)))
    ((IsScalarTower.toAlgHom K (A ⊗[K] B) (FractionRing (A ⊗[K] B))).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B))
    (fun _ _ ↦ Commute.all _ _)

private lemma tensorToFraction_comp :
    (tensorToFraction K A F B).comp (tensorFractionMap K A F B) =
      IsScalarTower.toAlgHom K (A ⊗[K] B) (FractionRing (A ⊗[K] B)) := by
  ext a
  · simp [tensorToFraction, tensorFractionMap, ← Algebra.TensorProduct.one_def]
    have : Nontrivial B :=
      (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom.domain_nontrivial
    have hi := Algebra.TensorProduct.includeLeft_injective
      (R := K) (S := K) (A := A) (B := B) (algebraMap K B).injective
    have hg := (IsFractionRing.injective (A ⊗[K] B) (FractionRing (A ⊗[K] B))).comp hi
    change IsFractionRing.lift (K := F) hg (algebraMap A F a) = _
    exact IsFractionRing.lift_algebraMap hg a
  · simp [tensorToFraction, tensorFractionMap]

/-- Passing one factor of an integral tensor product to its fraction field
preserves the fraction field of the tensor product. -/
def tensorFractionEquiv :
    FractionRing (F ⊗[K] B) ≃ₐ[K] FractionRing (A ⊗[K] B) := by
  let : Algebra (A ⊗[K] B) (F ⊗[K] B) := (tensorFractionMap K A F B).toAlgebra
  have : IsScalarTower A (A ⊗[K] B) (F ⊗[K] B) :=
    .of_algebraMap_eq fun a ↦ by
      simp [tensorFractionMap, RingHom.algebraMap_toAlgebra,
        Algebra.TensorProduct.algebraMap_apply]
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[K] B) (nonZeroDivisors A))
      (F ⊗[K] B) :=
    IsLocalization.tensorProduct_tensorProduct K B (nonZeroDivisors A) F (by
      ext b
      simp [tensorFractionMap, RingHom.algebraMap_toAlgebra])
  let : Algebra (F ⊗[K] B) (FractionRing (A ⊗[K] B)) :=
    (tensorToFraction K A F B).toAlgebra
  have : IsScalarTower (A ⊗[K] B) (F ⊗[K] B) (FractionRing (A ⊗[K] B)) :=
    .of_algebraMap_eq' (congrArg AlgHom.toRingHom (tensorToFraction_comp K A F B)).symm
  have : IsFractionRing (F ⊗[K] B) (FractionRing (A ⊗[K] B)) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid (A ⊗[K] B) (nonZeroDivisors A)) _ _
  exact (IsLocalization.algEquiv (nonZeroDivisors (F ⊗[K] B))
    (FractionRing (F ⊗[K] B)) (FractionRing (A ⊗[K] B))).restrictScalars K

end

end GroupActions
