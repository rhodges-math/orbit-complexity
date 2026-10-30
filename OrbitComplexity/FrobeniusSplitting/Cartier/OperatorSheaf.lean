import OrbitComplexity.FrobeniusSplitting.Cartier.InputAction

/-! # The module sheaf of local linear operators with input multiplication -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

variable {X : Scheme.{u}} (α : X.ringCatSheaf ⟶ X.ringCatSheaf)

private abbrev sourceModule : X.Modules :=
  (SheafOfModules.restrictScalars α).obj (SheafOfModules.unit X.ringCatSheaf)

private abbrev targetModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

private def sectionRestriction {U V : X.Opens} (f : V ⟶ U) :
    Γ(X, U) →+* Γ(X, V) := (X.presheaf.map f.op).hom

private def restrictOperators {U V : X.Opens} (f : V ⟶ U)
    (φ : localOperators α U) : localOperators α V where
  val.app W := φ.val.app (op ((Over.map f).obj W.unop))
  val.naturality g := φ.val.naturality ((Over.map f).map g.unop).op

private theorem restrictOperators_smul {U V : X.Opens} (f : V ⟶ U)
    (a : Γ(X, U)) (φ : localOperators α U) :
    restrictOperators α f (a • φ) =
      X.presheaf.map f.op a • restrictOperators α f φ := by
  ext W m
  change (φ.val.app (op ((Over.map f).obj W.unop))).hom
      (X.presheaf.map (W.unop.hom ≫ f).op a *
        (show Γ(X, W.unop.left) from m)) =
    (φ.val.app (op ((Over.map f).obj W.unop))).hom
      (X.presheaf.map W.unop.hom.op (X.presheaf.map f.op a) *
        (show Γ(X, W.unop.left) from m))
  congr 2
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

private def operatorPresheaf : PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj U := ModuleCat.of Γ(X, U.unop) (localOperators α U.unop)
  map {U V} f := ModuleCat.ofHom
    (X := ModuleCat.of Γ(X, U.unop) (localOperators α U.unop))
    (Y := (ModuleCat.restrictScalars (sectionRestriction f.unop)).obj
      (ModuleCat.of Γ(X, V.unop) (localOperators α V.unop)))
    { toFun := restrictOperators α f.unop
      map_add' := fun φ ψ => by
        change restrictOperators α f.unop (φ + ψ) =
          restrictOperators α f.unop φ + restrictOperators α f.unop ψ
        ext W m
        rfl
      map_smul' := fun a φ => restrictOperators_smul α f.unop a φ }
  map_id U := by rfl
  map_comp f g := by rfl

private def operatorSetIso :
    (operatorPresheaf α).presheaf ⋙ forget AddCommGrpCat ≅
      (SheafOfModules.linearHom (sourceModule α) (targetModule (X := X))).obj :=
  NatIso.ofComponents
    (fun U => ((SheafOfModules.linearHomObjEquiv
      (sourceModule α) (targetModule (X := X)) U.unop).symm).toIso)
    (by
      intro U V f
      apply ConcreteCategory.hom_ext
      intro φ
      change (SheafOfModules.linearHomObjEquiv
          (sourceModule α) (targetModule (X := X)) V.unop).symm
          (restrictOperators α f.unop φ) =
        (SheafOfModules.linearHom (sourceModule α) (targetModule (X := X))).obj.map f
          ((SheafOfModules.linearHomObjEquiv
            (sourceModule α) (targetModule (X := X)) U.unop).symm φ)
      apply (SheafOfModules.linearHomObjEquiv
        (sourceModule α) (targetModule (X := X)) V.unop).injective
      rw [Equiv.apply_symm_apply]
      ext W m
      have h := SheafOfModules.linearHomObjEquiv_map_app
        (sourceModule α) (targetModule (X := X)) f.unop W.unop.hom
        ((SheafOfModules.linearHomObjEquiv
          (sourceModule α) (targetModule (X := X)) U.unop).symm φ)
        (show (sourceModule α).val.obj (op W.unop.left) from m)
      have hc := congrArg
        (fun ψ : (sourceModule α).over U.unop ⟶ (targetModule (X := X)).over U.unop =>
          (ψ.val.app (op (Over.mk (W.unop.hom ≫ f.unop)))).hom
            (show (sourceModule α).val.obj (op W.unop.left) from m))
        ((SheafOfModules.linearHomObjEquiv
          (sourceModule α) (targetModule (X := X)) U.unop).apply_symm_apply φ)
      exact hc.symm.trans h.symm)

/-- The sheaf of local O-linear operators with scalars acting on their inputs. -/
def operatorModule : X.Modules where
  val := operatorPresheaf α
  isSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp (Opens.grothendieckTopology X)
      (s := forget AddCommGrpCat)
    exact (Presheaf.isSheaf_of_iso_iff (operatorSetIso α)).mpr
      (SheafOfModules.linearHom (sourceModule α) (targetModule (X := X))).property

/-- Sections are the O-linear morphisms between the restricted module sheaves. -/
def operatorModuleSections (U : X.Opens) :
    (operatorModule α).val.obj (op U) ≃
      ((sourceModule α).over U ⟶ (targetModule (X := X)).over U) := Equiv.refl _

/-- Scalar multiplication in the operator sheaf multiplies the argument of the operator. -/
theorem operatorModule_smul (U : X.Opens) (a : Γ(X, U))
    (φ : (operatorModule α).val.obj (op U)) (V : Over U) (m : Γ(X, V.left)) :
    ((operatorModuleSections α U (((operatorModule α).smul a).hom φ)).val.app
      (op V)).hom m =
      ((operatorModuleSections α U φ).val.app (op V)).hom
        (X.presheaf.map V.hom.op a * m) := rfl

end FrobeniusSplitting.OperatorSheaf
