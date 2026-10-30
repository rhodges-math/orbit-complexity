import OrbitComplexity.FrobeniusSplitting.Cartier.OperatorSheaf
import OrbitComplexity.FrobeniusSplitting.Splittings.CartierCoordinates
import OrbitComplexity.FrobeniusSplitting.Splittings.Perfect
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorMorphisms

/-! # The trace frame as a morphism into the operator sheaf -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

private abbrev unitSheaf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private abbrev sourceModule {X : Scheme.{u}}
    (α : X.ringCatSheaf ⟶ X.ringCatSheaf) : X.Modules :=
  (SheafOfModules.restrictScalars α).obj (unitSheaf X)

private def fromSchemeOperator (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (φ : SchemeFrobeniusMap X p) :
    sourceModule (sheafFrobenius C p base) ⟶ unitSheaf X where
  val.app U := ModuleCat.ofHom
    (X := (sourceModule (sheafFrobenius C p base)).val.obj U)
    (Y := (unitSheaf X).val.obj U)
    { toFun := fun r => φ.onOpen U.unop (show Γ(X, U.unop) from r)
      map_add' := fun r s => (φ.onOpen U.unop).map_add _ _
      map_smul' := fun r s => by
        change φ.onOpen U.unop
            ((show Γ(X, U.unop) from r) ^ p * (show Γ(X, U.unop) from s)) =
          (show Γ(X, U.unop) from r) * φ.onOpen U.unop (show Γ(X, U.unop) from s)
        exact (φ.onOpen U.unop).map_pow_mul _ _ }
  val.naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext r
    exact φ.restrict_comm (leOfHom f.unop) (show Γ(X, U.unop) from r)

private def globalOperatorSection {X : Scheme.{u}}
    (α : X.ringCatSheaf ⟶ X.ringCatSheaf) (T : sourceModule α ⟶ unitSheaf X) :
    (operatorModule α).sections where
  val U := T.over U.unop
  property {U V} f := by
    change (show localOperators α V.unop from
        ((operatorModule α).val.map f).hom (T.over U.unop)) = T.over V.unop
    ext W m
    rfl

private def globalOperatorFrame {X : Scheme.{u}}
    (α : X.ringCatSheaf ⟶ X.ringCatSheaf) (T : sourceModule α ⟶ unitSheaf X) :
    unitSheaf X ⟶ operatorModule α :=
  (operatorModule α).unitHomEquiv.symm (globalOperatorSection α T)

private theorem globalOperatorFrame_apply {X : Scheme.{u}}
    (α : X.ringCatSheaf ⟶ X.ringCatSheaf) (T : sourceModule α ⟶ unitSheaf X)
    (U : X.Opens) (r : Γ(X, U)) (V : Over U) (m : Γ(X, V.left)) :
    ((operatorModuleSections α U
      (((globalOperatorFrame α T).val.app (op U)).hom r)).val.app (op V)).hom m =
      (T.val.app (op V.left)).hom (X.presheaf.map V.hom.op r * m) := rfl

private abbrev affineLine (C : Type u) [CommRing C] := Spec (.of (Polynomial C))

private def affineBase (C : Type u) [CommRing C] : affineLine C ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : C →+* Polynomial C))

private def affineTrace (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    [PerfectRing C p] : SchemeFrobeniusMap (affineLine C) p :=
  (univariateTrace (RingSplitting.ofPerfectRing C p)).toSpec (expChar_pos C p)

/-- The canonical affine trace defines a morphism into the sheaf of all local operators. -/
def affineTraceFrame (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    [PerfectRing C p] :
    unitSheaf (affineLine C) ⟶ operatorModule (sheafFrobenius C p (affineBase C)) :=
  globalOperatorFrame (sheafFrobenius C p (affineBase C))
    (fromSchemeOperator C p (affineBase C) (affineTrace C p))

/-- On every smaller open, the frame multiplies the argument before applying the trace. -/
theorem affineTraceFrame_apply (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    [PerfectRing C p] (U : (affineLine C).Opens) (r : Γ(affineLine C, U))
    (V : Over U) (m : Γ(affineLine C, V.left)) :
    ((operatorModuleSections (sheafFrobenius C p (affineBase C)) U
      (((affineTraceFrame C p).val.app (op U)).hom r)).val.app (op V)).hom m =
      (affineTrace C p).onOpen V.left ((affineLine C).presheaf.map V.hom.op r * m) :=
  globalOperatorFrame_apply (sheafFrobenius C p (affineBase C))
    (fromSchemeOperator C p (affineBase C) (affineTrace C p)) U r V m

end FrobeniusSplitting.OperatorSheaf
