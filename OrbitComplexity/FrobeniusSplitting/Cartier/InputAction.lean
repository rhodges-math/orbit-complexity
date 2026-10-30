import TauCeti.Algebra.Category.ModuleCat.Sheaf.Hom
import OrbitComplexity.FrobeniusSplitting.Modules.Frobenius
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Input multiplication on local linear operators -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

variable {X : Scheme.{u}} (α : X.ringCatSheaf ⟶ X.ringCatSheaf)

private abbrev unitSheaf : X.Modules := SheafOfModules.unit X.ringCatSheaf

private abbrev twistedUnit : X.Modules :=
  (SheafOfModules.restrictScalars α).obj (unitSheaf (X := X))

/-- Local structure-sheaf operators linear for the restricted source scalars. -/
abbrev localOperators (U : X.Opens) :=
  (twistedUnit α).over U ⟶ (unitSheaf (X := X)).over U

private def inputMultiply (U : X.Opens) (a : Γ(X, U)) :
    (twistedUnit α).over U ⟶ (twistedUnit α).over U where
  val.app V := ModuleCat.ofHom
    (X := ((twistedUnit α).over U).val.obj V)
    (Y := ((twistedUnit α).over U).val.obj V)
    { toFun := fun m =>
        X.presheaf.map V.unop.hom.op a * (show Γ(X, V.unop.left) from m)
      map_add' := fun m n => by
        change X.presheaf.map V.unop.hom.op a *
            ((show Γ(X, V.unop.left) from m) + (show Γ(X, V.unop.left) from n)) =
          X.presheaf.map V.unop.hom.op a * (show Γ(X, V.unop.left) from m) +
            X.presheaf.map V.unop.hom.op a * (show Γ(X, V.unop.left) from n)
        exact mul_add _ _ _
      map_smul' := fun r m => by
        change X.presheaf.map V.unop.hom.op a *
            ((show Γ(X, V.unop.left) from (α.hom.app (op V.unop.left)).hom r) *
              (show Γ(X, V.unop.left) from m)) =
          (show Γ(X, V.unop.left) from (α.hom.app (op V.unop.left)).hom r) *
            (X.presheaf.map V.unop.hom.op a * (show Γ(X, V.unop.left) from m))
        ring }
  val.naturality {V W} f := by
    apply ModuleCat.hom_ext
    ext m
    change X.presheaf.map W.unop.hom.op a *
        X.presheaf.map f.unop.left.op (show Γ(X, V.unop.left) from m) =
      X.presheaf.map f.unop.left.op
        (X.presheaf.map V.unop.hom.op a * (show Γ(X, V.unop.left) from m))
    symm
    rw [map_mul]
    congr 1
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    congr 1

private theorem inputMultiply_one (U : X.Opens) :
    inputMultiply α U 1 = 𝟙 _ := by
  ext V m
  change X.presheaf.map V.unop.hom.op (1 : Γ(X, U)) *
    (show Γ(X, V.unop.left) from m) = m
  rw [map_one, one_mul]

private theorem inputMultiply_zero (U : X.Opens) :
    inputMultiply α U 0 = 0 := by
  ext V m
  change X.presheaf.map V.unop.hom.op (0 : Γ(X, U)) *
    (show Γ(X, V.unop.left) from m) = 0
  rw [map_zero, zero_mul]

private theorem inputMultiply_add (U : X.Opens) (a b : Γ(X, U)) :
    inputMultiply α U (a + b) = inputMultiply α U a + inputMultiply α U b := by
  ext V m
  change X.presheaf.map V.unop.hom.op (a + b) *
      (show Γ(X, V.unop.left) from m) =
    X.presheaf.map V.unop.hom.op a * (show Γ(X, V.unop.left) from m) +
      X.presheaf.map V.unop.hom.op b * (show Γ(X, V.unop.left) from m)
  rw [map_add, add_mul]

private theorem inputMultiply_mul (U : X.Opens) (a b : Γ(X, U)) :
    inputMultiply α U (a * b) = inputMultiply α U a ≫ inputMultiply α U b := by
  ext V m
  change X.presheaf.map V.unop.hom.op (a * b) *
      (show Γ(X, V.unop.left) from m) =
    X.presheaf.map V.unop.hom.op b *
      (X.presheaf.map V.unop.hom.op a * (show Γ(X, V.unop.left) from m))
  rw [map_mul]
  ring

/-- A section acts on a local operator by multiplying its input. -/
instance inputModule (U : X.Opens) : Module Γ(X, U) (localOperators α U) where
  smul a φ := inputMultiply α U a ≫ φ
  one_smul φ :=
    (congrArg (fun f => f ≫ φ) (inputMultiply_one α U)).trans (Category.id_comp φ)
  mul_smul a b φ :=
    (congrArg (fun f => f ≫ φ) (inputMultiply_mul α U a b)).trans
      (Category.assoc _ _ φ)
  add_smul a b φ :=
    (congrArg (fun f => f ≫ φ) (inputMultiply_add α U a b)).trans
      (Preadditive.add_comp _ _ _ _ _ φ)
  smul_add a φ ψ := Preadditive.comp_add _ _ _ (inputMultiply α U a) φ ψ
  zero_smul φ :=
    (congrArg (fun f => f ≫ φ) (inputMultiply_zero α U)).trans
      (Limits.zero_comp (f := φ))
  smul_zero a := Limits.comp_zero (f := inputMultiply α U a)

/-- Input multiplication acts before the operator on every smaller open. -/
theorem inputModule_apply (U : X.Opens) (a : Γ(X, U)) (φ : localOperators α U)
    (V : CategoryTheory.Over U) (m : Γ(X, V.left)) :
    ((a • φ).val.app (op V)).hom m =
      (φ.val.app (op V)).hom (X.presheaf.map V.hom.op a * m) := rfl

end FrobeniusSplitting.OperatorSheaf
