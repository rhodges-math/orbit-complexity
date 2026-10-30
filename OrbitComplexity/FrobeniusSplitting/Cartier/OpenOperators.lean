import OrbitComplexity.FrobeniusSplitting.Cartier.OperatorSheaf
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorTransport
import Mathlib.CategoryTheory.HomCongr

/-! # Local operators on an open subscheme -/

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u

namespace FrobeniusSplitting.OperatorSheaf

private abbrev O (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

private abbrev source (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) : X.Modules :=
  (SheafOfModules.restrictScalars (sheafFrobenius C p base)).obj (O X)

private def toOperator (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (φ : source C p base ⟶ O X) : SchemeFrobeniusMap X p where
  onOpen (U : X.Opens) :=
    { toAddMonoidHom :=
        { toFun := fun (r : Γ(X, U)) => (show Γ(X, U) from (φ.val.app (op U)).hom r)
          map_zero' := (φ.val.app (op U)).hom.map_zero
          map_add' := (φ.val.app (op U)).hom.map_add }
      map_pow_mul' (a b : Γ(X, U)) := by
        exact (φ.val.app (op U)).hom.map_smul a b }
  restrict_comm h s := PresheafOfModules.naturality_apply φ.val (homOfLE h).op s

private def fromOperator (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (φ : SchemeFrobeniusMap X p) : source C p base ⟶ O X where
  val.app (U : X.Opensᵒᵖ) := ModuleCat.ofHom
    (X := (source C p base).val.obj U) (Y := (O X).val.obj U)
    { toFun := fun r => φ.onOpen U.unop (show Γ(X, U.unop) from r)
      map_add' := fun r s => (φ.onOpen U.unop).map_add _ _
      map_smul' := fun r s => (φ.onOpen U.unop).map_pow_mul _ _ }
  val.naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext r
    exact φ.restrict_comm (leOfHom f.unop) (show Γ(X, U.unop) from r)

private theorem from_toOperator (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (φ : source C p base ⟶ O X) :
    fromOperator C p base (toOperator C p base φ) = φ := by
  ext U r
  rfl

private theorem to_fromOperator (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (φ : SchemeFrobeniusMap X p) :
    toOperator C p base (fromOperator C p base φ) = φ := by
  ext U r
  rfl

private def globalEquiv (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) :
    (source C p base ⟶ O X) ≃ SchemeFrobeniusMap X p where
  toFun := toOperator C p base
  invFun := fromOperator C p base
  left_inv := from_toOperator C p base
  right_inv := to_fromOperator C p base

private def openSourceIso (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens) :
    (Scheme.Modules.overEquiv U).functor.obj ((source C p base).over U) ≅
      source C p (U.ι ≫ base) :=
  Iso.refl _

private def openTargetIso {X : Scheme.{u}} (U : X.Opens) :
    (Scheme.Modules.overEquiv U).functor.obj ((O X).over U) ≅ O U.toScheme :=
  Iso.refl _

/-- Local linear sheaf operators correspond to Frobenius operators on the open subscheme. -/
def openOperatorEquiv (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens) :
    localOperators (sheafFrobenius C p base) U ≃ SchemeFrobeniusMap U.toScheme p :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv.trans
    ((Iso.homCongr (openSourceIso C p base U) (openTargetIso U)).trans
      (globalEquiv C p (U.ι ≫ base)))

/-- A source-open image regarded as an open contained in its ambient open. -/
private def imageIn {X : Scheme.{u}} (U : X.Opens) (V : U.toScheme.Opens) : Over U :=
  Over.mk (homOfLE (by
    simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange V))

/-- The correspondence evaluates the original sheaf morphism on the image open. -/
theorem openOperatorEquiv_apply (C : Type u) [CommRing C] (p : ℕ) [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens)
    (φ : localOperators (sheafFrobenius C p base) U)
    (V : U.toScheme.Opens) (m : Γ(U.toScheme, V)) :
    (openOperatorEquiv C p base U φ).onOpen V m =
      (φ.val.app (op (imageIn U V))).hom m := by
  rfl

end FrobeniusSplitting.OperatorSheaf
