import OrbitComplexity.GroupActions.Varieties.PointDerivations
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Product

/-! # Point derivations at the counit

The coefficient algebra of the counit point agrees with the counit coefficient algebra used
for affine-group tangent Lie algebras. Their derivation spaces consequently identify linearly.

## Main definitions

* `GroupActions.counitPointCoefficientEquiv`: the comparison of coefficient modules.
* `GroupActions.counitPointDerivEquiv`: the comparison of derivation spaces.
-/

namespace GroupActions

noncomputable section

universe u v

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The counit point coefficient module is the counit coefficient module of the bialgebra. -/
def counitPointCoefficientEquiv :
    PointAlgebra (Bialgebra.counitAlgHom R A) ≃ₗ[A] TauCeti.Bialgebra.CounitAlgebra R A R where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    let z : R := PointAlgebra.algEquivSelf (Bialgebra.counitAlgHom R A) x
    change (Bialgebra.counitAlgHom R A a * z : R) =
      algebraMap R R (Coalgebra.counit (R := R) a) * z
    simp only [Bialgebra.counitAlgHom_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- Derivations at the counit point identify with the bialgebra's tangent derivations. -/
def counitPointDerivEquiv :
    Derivation R A (PointAlgebra (Bialgebra.counitAlgHom R A)) ≃ₗ[R]
      Derivation R A (TauCeti.Bialgebra.CounitAlgebra R A R) where
  toEquiv := (counitPointCoefficientEquiv R A).compDer.toEquiv
  map_add' d e := by ext a; rfl
  map_smul' r d := by ext a; rfl

/-- The coefficient comparison preserves evaluation of tangent derivations. -/
@[simp]
theorem counitPointDerivEquiv_apply
    (d : Derivation R A (PointAlgebra (Bialgebra.counitAlgHom R A))) (a : A) :
    counitPointDerivEquiv R A d a = d a := rfl

/-- The inverse coefficient comparison preserves evaluation of tangent derivations. -/
@[simp]
theorem counitPointDerivEquiv_symm_apply
    (d : Derivation R A (TauCeti.Bialgebra.CounitAlgebra R A R)) (a : A) :
    (counitPointDerivEquiv R A).symm d a = d a := rfl

end

end GroupActions
