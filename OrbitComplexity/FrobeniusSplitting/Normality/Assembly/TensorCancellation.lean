import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FixedScalarCocone
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.CategoryTheory.Whiskering
import Batteries.Tactic.Lint

/-! # Cancellation of an intermediate scalar extension

The canonical tensor cancellation commutes with coefficient maps, units and
polynomials, and identifies the diagrams obtained by one or two extensions.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open CategoryTheory
open scoped TensorProduct

namespace FrobeniusSplitting

variable (S R T : Type u) [CommRing S] [CommRing R] [CommRing T]
    [Algebra S R] [Algebra R T] [Algebra S T] [IsScalarTower S R T]

/-- Cancellation of the intermediate coefficient ring. -/
def tensorCancelEquiv (A : Type u) [CommRing A] [Algebra S A] :
    T ⊗[R] (R ⊗[S] A) ≃ₐ[T] T ⊗[S] A :=
  Algebra.TensorProduct.cancelBaseChange S R T T A

variable {S R T}
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra S A] [Algebra S B]

private def twiceTensorMap (f : A →ₐ[S] B) :
    T ⊗[R] (R ⊗[S] A) →ₐ[T] T ⊗[R] (R ⊗[S] B) :=
  Algebra.TensorProduct.map (AlgHom.id T T)
    (Algebra.TensorProduct.map (AlgHom.id R R) f)

/-- Tensor cancellation is natural in the coefficient algebra. -/
theorem tensorCancel_natural (f : A →ₐ[S] B) :
    (tensorCancelEquiv S R T B).toAlgHom.comp (twiceTensorMap (R := R) (T := T) f) =
      (Algebra.TensorProduct.map (AlgHom.id T T) f).comp
        (tensorCancelEquiv S R T A).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro t z
  induction z using TensorProduct.inductionOn with
  | tmul r a => simp [tensorCancelEquiv, twiceTensorMap]
  | add x y hx hy => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy

/-- The two coefficient inclusions become the original inclusion after cancellation. -/
theorem tensorCancel_inclusions :
    ((tensorCancelEquiv S R T A).toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom).comp
          (Algebra.TensorProduct.includeRight : A →ₐ[S] R ⊗[S] A).toRingHom =
      (Algebra.TensorProduct.includeRight : A →ₐ[S] T ⊗[S] A).toRingHom := by
  ext a
  simp [tensorCancelEquiv]

/-- Cancellation preserves the units transported through both scalar extensions. -/
theorem tensorCancel_units (a : Aˣ) :
    Units.map (tensorCancelEquiv S R T A).toRingHom.toMonoidHom
      (Units.map (Algebra.TensorProduct.includeRight :
        R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom.toMonoidHom
          (Units.map (Algebra.TensorProduct.includeRight :
            A →ₐ[S] R ⊗[S] A).toRingHom.toMonoidHom a)) =
      Units.map (Algebra.TensorProduct.includeRight :
        A →ₐ[S] T ⊗[S] A).toRingHom.toMonoidHom a := by
  apply Units.ext
  exact DFunLike.congr_fun (tensorCancel_inclusions (S := S) (R := R) (T := T)) (a : A)

/-- Cancellation preserves the polynomial transported through both scalar extensions. -/
theorem tensorCancel_polynomial (P : Polynomial A) :
    Polynomial.map (tensorCancelEquiv S R T A).toRingHom
      (Polynomial.map (Algebra.TensorProduct.includeRight :
        R ⊗[S] A →ₐ[R] T ⊗[R] (R ⊗[S] A)).toRingHom
          (Polynomial.map (Algebra.TensorProduct.includeRight :
            A →ₐ[S] R ⊗[S] A).toRingHom P)) =
      Polynomial.map (Algebra.TensorProduct.includeRight :
        A →ₐ[S] T ⊗[S] A).toRingHom P := by
  rw [Polynomial.map_map, Polynomial.map_map]
  exact congrArg (fun f => Polynomial.map f P)
    (tensorCancel_inclusions (S := S) (R := R) (T := T))

/-- One and two scalar extensions give canonically isomorphic coefficient diagrams. -/
def tensorCancellationIso {J : Type v} [Category.{w} J]
    (N : J ⥤ CommAlgCat.{u} S) :
    fixedFibreDiagram (R := T) (M := T)
      (fixedFibreDiagram (R := R) (M := R) N) ≅
        fixedFibreDiagram (R := T) (M := T) N :=
  NatIso.ofComponents
    (fun j => CommAlgCat.isoMk (tensorCancelEquiv S R T (N.obj j)))
    (by
      intro i j f
      apply CommAlgCat.hom_ext
      exact tensorCancel_natural (R := R) (T := T) (N.map f).hom)

/-- The diagram cancellation intertwines the original scalar inclusion maps. -/
theorem tensorCancellation_scalar {J : Type v} [Category.{w} J]
    (N : J ⥤ CommAlgCat.{u} S) :
    (fixedScalarMap S R N ≫
      fixedScalarMap R T (fixedFibreDiagram (R := R) (M := R) N)) ≫
        Functor.whiskerRight (tensorCancellationIso (R := R) (T := T) N).hom
          (forget₂ (CommAlgCat T) CommRingCat) = fixedScalarMap S T N := by
  apply NatTrans.ext
  funext j
  apply CommRingCat.hom_ext
  exact tensorCancel_inclusions (S := S) (R := R) (T := T) (A := N.obj j)

end FrobeniusSplitting
