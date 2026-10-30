import OrbitComplexity.GroupActions.Varieties.DifferentialMaps

/-! # Derivations at algebra points

A point induces a coordinate-algebra action on its coefficient ring. Keeping this action on
a coefficient synonym permits simultaneous derivations at different points of the same algebra.

## Main definitions

* `GroupActions.PointAlgebra`: a coefficient algebra carrying the scalar action of a point.
* `GroupActions.pointDerivationPrecomp`: precomposition of point-valued derivations.
-/

namespace GroupActions

noncomputable section

universe u v w x

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The coefficient ring of an algebra point, with the coordinate algebra acting through it. -/
def PointAlgebra (_f : A →ₐ[R] B) : Type w := B

namespace PointAlgebra

variable (f : A →ₐ[R] B)

/-- The coefficient synonym inherits its commutative ring structure. -/
instance commRing : CommRing (PointAlgebra f) := inferInstanceAs (CommRing B)

/-- The ground ring acts on the coefficient synonym through its coefficient algebra. -/
instance baseAlgebra : Algebra R (PointAlgebra f) := inferInstanceAs (Algebra R B)

/-- The coefficient ring acts on its point synonym by multiplication. -/
instance (priority := 100) coefficientAlgebra : Algebra B (PointAlgebra f) :=
  inferInstanceAs (Algebra B B)

/-- The coordinate algebra acts on the coefficient synonym through the point. -/
instance coordinateAlgebra : Algebra A (PointAlgebra f) := f.toRingHom.toAlgebra

/-- The ground-ring action agrees with its action through the coordinate algebra. -/
instance coordinateTower : IsScalarTower R A (PointAlgebra f) :=
  IsScalarTower.of_algebraMap_eq fun r => f.commutes r |>.symm

/-- The ground-ring action agrees with its action through the coefficient algebra. -/
instance coefficientTower : IsScalarTower R B (PointAlgebra f) :=
  inferInstanceAs (IsScalarTower R B B)

/-- Coordinate and coefficient scalars commute on the point synonym. -/
instance coefficientComm : SMulCommClass B A (PointAlgebra f) where
  smul_comm b a y := by
    let z : B := y
    change b * (f a * z) = f a * (b * z)
    ring

/-- The coefficient synonym is the original coefficient algebra over the ground ring. -/
def algEquivSelf : PointAlgebra f ≃ₐ[R] B := AlgEquiv.refl

/-- The coordinate scalar action on a coefficient is multiplication by the point value. -/
theorem smul_apply (a : A) (y : PointAlgebra f) :
    algEquivSelf f (a • y) = f a * algEquivSelf f y := rfl

end PointAlgebra

variable {C : Type x} [CommRing C] [Algebra R C]

/-- Precompose a derivation at a point with a morphism of coordinate algebras. -/
def pointDerivationPrecomp (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    Derivation R B (PointAlgebra g) →ₗ[C] Derivation R A (PointAlgebra (g.comp f)) where
  toFun d :=
    { toLinearMap := (PointAlgebra.algEquivSelf (g.comp f)).symm.toLinearMap.comp
        ((PointAlgebra.algEquivSelf g).toLinearMap.comp (d.toLinearMap.comp f.toLinearMap))
      map_one_eq_zero' := by
        simp
      leibniz' a b := by
        apply (PointAlgebra.algEquivSelf (g.comp f)).injective
        simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
          AlgEquiv.apply_symm_apply, AlgHom.toLinearMap_apply, map_mul,
          map_add, PointAlgebra.smul_apply, AlgHom.comp_apply]
        exact congrArg (PointAlgebra.algEquivSelf g) (d.leibniz (f a) (f b)) |>.trans
          (by simp only [map_add, PointAlgebra.smul_apply]; rfl) }
  map_add' d e := by ext a; rfl
  map_smul' c d := by ext a; rfl

/-- Precomposition evaluates a point derivation on the coordinate image. -/
@[simp]
theorem pointDerivationPrecomp_apply (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (d : Derivation R B (PointAlgebra g)) (a : A) :
    pointDerivationPrecomp f g d a = d (f a) := rfl

/-- An equivalence of coordinate algebras transports derivations at the corresponding points. -/
def pointDerivationEquiv (e : A ≃ₐ[R] B) (g : B →ₐ[R] C) :
    Derivation R B (PointAlgebra g) ≃ₗ[C]
      Derivation R A (PointAlgebra (g.comp e.toAlgHom)) where
  toLinearMap := pointDerivationPrecomp e.toAlgHom g
  invFun d :=
    { toLinearMap := (PointAlgebra.algEquivSelf g).symm.toLinearMap.comp
        ((PointAlgebra.algEquivSelf (g.comp e.toAlgHom)).toLinearMap.comp
          (d.toLinearMap.comp e.symm.toAlgHom.toLinearMap))
      map_one_eq_zero' := by
        simp
      leibniz' a b := by
        apply (PointAlgebra.algEquivSelf g).injective
        simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
          AlgEquiv.apply_symm_apply, AlgHom.toLinearMap_apply, map_mul,
          map_add, PointAlgebra.smul_apply]
        have hd := congrArg (PointAlgebra.algEquivSelf (g.comp e.toAlgHom))
          (d.leibniz (e.symm a) (e.symm b))
        simpa only [map_add, PointAlgebra.smul_apply, AlgHom.comp_apply,
          AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, Derivation.coeFn_coe] using hd }
  left_inv d := by
    ext b
    change d (e (e.symm b)) = d b
    rw [e.apply_symm_apply]
  right_inv d := by
    ext a
    change d (e.symm (e a)) = d a
    rw [e.symm_apply_apply]

section Towers

/-- Equal points have canonically identical derivation spaces. -/
def pointDerivationCongr {f g : A →ₐ[R] B} (h : f = g) :
    Derivation R A (PointAlgebra f) ≃ₗ[B] Derivation R A (PointAlgebra g) := by
  subst g
  exact LinearEquiv.refl B _

/-- Transport along equality of points preserves the value of a derivation. -/
@[simp]
theorem pointDerivationCongr_apply {f g : A →ₐ[R] B} (h : f = g)
    (d : Derivation R A (PointAlgebra f)) (a : A) :
    pointDerivationCongr h d a = d a := by subst g; rfl

variable (R A B) [Algebra A B] [IsScalarTower R A B]

/-- For a point given by an algebra tower, the coefficient synonym has its scalar action. -/
def pointCoefficientLinearEquiv :
    PointAlgebra (IsScalarTower.toAlgHom R A B) ≃ₗ[A] B where
  toEquiv := (PointAlgebra.algEquivSelf (IsScalarTower.toAlgHom R A B)).toEquiv
  map_add' x y := rfl
  map_smul' a y := by
    let z : B := PointAlgebra.algEquivSelf (IsScalarTower.toAlgHom R A B) y
    change algebraMap A B a * z = a • z
    rw [Algebra.smul_def]

/-- Point derivations for an algebra tower are its usual coefficient-valued derivations. -/
def pointDerivationOfTower :
    Derivation R A (PointAlgebra (IsScalarTower.toAlgHom R A B)) ≃ₗ[B] Derivation R A B where
  toEquiv := (pointCoefficientLinearEquiv R A B).compDer.toEquiv
  map_add' d e := by ext a; rfl
  map_smul' b d := by ext a; rfl

/-- Comparing point derivations with a tower preserves evaluation. -/
@[simp]
theorem pointDerivationOfTower_apply
    (d : Derivation R A (PointAlgebra (IsScalarTower.toAlgHom R A B))) (a : A) :
    pointDerivationOfTower R A B d a = d a := rfl

end Towers

section Naturality

variable (R A B C) [Algebra A B] [Algebra A C] [Algebra B C]
  [IsScalarTower R A B] [IsScalarTower R A C] [IsScalarTower R B C] [IsScalarTower A B C]

/-- The point of an algebra tower is the composition of its two constituent points. -/
theorem pointOfTower_comp :
    (IsScalarTower.toAlgHom R B C).comp (IsScalarTower.toAlgHom R A B) =
      IsScalarTower.toAlgHom R A C := by
  ext a
  exact (IsScalarTower.algebraMap_apply A B C a).symm

/-- Comparing point derivations with tower derivations commutes with precomposition. -/
theorem pointDerivationOfTower_comp
    (d : Derivation R B (PointAlgebra (IsScalarTower.toAlgHom R B C))) :
    pointDerivationOfTower R A C
        (pointDerivationCongr (pointOfTower_comp R A B C)
          (pointDerivationPrecomp (IsScalarTower.toAlgHom R A B)
            (IsScalarTower.toAlgHom R B C) d)) =
      (pointDerivationOfTower R B C d).compAlgebraMap A := by
  apply Derivation.ext
  intro a
  simp only [pointDerivationOfTower_apply, pointDerivationCongr_apply,
    pointDerivationPrecomp_apply, Derivation.compAlgebraMap_apply]
  rfl

end Naturality

end

end GroupActions
