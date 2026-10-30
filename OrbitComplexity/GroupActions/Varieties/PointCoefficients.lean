import OrbitComplexity.GroupActions.Varieties.PointDerivations

/-! # Changing coefficients of point derivations

An equivalence of coefficient algebras transports the scalar action of a point and its
derivations. This transport commutes with precomposition of coordinate functions.

## Main definitions

* `GroupActions.pointCoefficientEquiv`: equivalence of point coefficient modules.
* `GroupActions.pointDerivCoeffEquiv`: equivalence of point derivation spaces.
-/

namespace GroupActions

noncomputable section

universe u v w x

variable {R : Type u} {A : Type v} {C : Type w} {D : Type x}
  [CommRing R] [CommRing A] [CommRing C] [CommRing D]
  [Algebra R A] [Algebra R C] [Algebra R D]

/-- An equivalence of coefficient algebras identifies the modules at corresponding points. -/
def pointCoefficientEquiv (e : C ≃ₐ[R] D) (f : A →ₐ[R] C) :
    PointAlgebra f ≃ₗ[A] PointAlgebra (e.toAlgHom.comp f) where
  toEquiv := (PointAlgebra.algEquivSelf f).toEquiv.trans
    (e.toEquiv.trans (PointAlgebra.algEquivSelf (e.toAlgHom.comp f)).symm.toEquiv)
  map_add' x y := by
    change (PointAlgebra.algEquivSelf (e.toAlgHom.comp f)).symm
      (e (PointAlgebra.algEquivSelf f (x + y))) =
      (PointAlgebra.algEquivSelf (e.toAlgHom.comp f)).symm
        (e (PointAlgebra.algEquivSelf f x)) +
      (PointAlgebra.algEquivSelf (e.toAlgHom.comp f)).symm
        (e (PointAlgebra.algEquivSelf f y))
    simp only [map_add]
  map_smul' a x := by
    apply (PointAlgebra.algEquivSelf (e.toAlgHom.comp f)).injective
    change e (PointAlgebra.algEquivSelf f (a • x)) =
      e (f a) * e (PointAlgebra.algEquivSelf f x)
    rw [PointAlgebra.smul_apply, map_mul]

/-- Coefficient equivalence identifies derivations at corresponding algebra points. -/
def pointDerivCoeffEquiv (e : C ≃ₐ[R] D) (f : A →ₐ[R] C) :
    Derivation R A (PointAlgebra f) ≃ₗ[R]
      Derivation R A (PointAlgebra (e.toAlgHom.comp f)) :=
  (pointCoefficientEquiv e f).compDer.restrictScalars R

variable {B : Type*} [CommRing B] [Algebra R B]

/-- Changing point coefficients commutes with precomposition of coordinate functions. -/
theorem pointDerivCoeffEquiv_comp (e : C ≃ₐ[R] D) (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (d : Derivation R B (PointAlgebra g)) :
    pointDerivCoeffEquiv e (g.comp f) (pointDerivationPrecomp f g d) =
      pointDerivationPrecomp f (e.toAlgHom.comp g) (pointDerivCoeffEquiv e g d) := by
  ext a
  rfl

end

end GroupActions
