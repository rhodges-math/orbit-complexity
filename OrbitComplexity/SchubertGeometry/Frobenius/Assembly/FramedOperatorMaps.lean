import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedGluingSupport
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Line operators in a specified coframe

A coframe identifies morphisms with Frobenius-restricted line source with
operators on the open subscheme. The two constructions preserve the original
morphism, including its coefficient before insertion of a section.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private twistedOverMap twistedOverMap_comp_apply from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Express a line-source morphism in a specified coframe on an open subset. -/
def framedOpenOperator {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules) (U : X.Opens)
    (E : L.over U ≅ (unitModule X).over U)
    (k : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U) :
    SchemeFrobeniusMap U.toScheme p :=
  openOperatorEquiv C p base U
    (twistedOverMap base (unitModule X) L U E.inv ≫ k)

/-- Restore the line source of an operator using the specified coframe. -/
def coframedOpenMap {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules) (U : X.Opens)
    (E : L.over U ≅ (unitModule X).over U)
    (φ : SchemeFrobeniusMap U.toScheme p) :
    (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U :=
  twistedOverMap base L (unitModule X) U E.hom ≫
    (openOperatorEquiv C p base U).symm φ

/-- The restored map evaluates the coframe coefficient with the given operator. -/
theorem coframedOpenMap_apply {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules) (U : X.Opens)
    (E : L.over U ≅ (unitModule X).over U)
    (φ : SchemeFrobeniusMap U.toScheme p) (V : Over U) (m : Γ(L, V.left)) :
    ((coframedOpenMap base L U E φ).val.app (op V)).hom m =
      (((openOperatorEquiv C p base U).symm φ).val.app (op V)).hom
        ((E.hom.val.app (op V)).hom m) :=
  twistedOverMap_comp_apply base L (unitModule X) (unitModule X) U E.hom
    ((openOperatorEquiv C p base U).symm φ) V m

/-- Expressing and restoring a line map in the same coframe leaves it unchanged. -/
theorem coframedOpenMap_framed {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules) (U : X.Opens)
    (E : L.over U ≅ (unitModule X).over U)
    (k : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U) :
    coframedOpenMap base L U E (framedOpenOperator base L U E k) = k := by
  unfold coframedOpenMap framedOpenOperator
  rw [Equiv.symm_apply_apply]
  apply RelativeGlue.over_hom_ext (frobeniusRestriction C p base L) (unitModule X) U
  intro V m
  have h₁ := twistedOverMap_comp_apply base L (unitModule X) (unitModule X) U E.hom
    (twistedOverMap base (unitModule X) L U E.inv ≫ k) V m
  have h₂ := twistedOverMap_comp_apply base (unitModule X) L (unitModule X) U E.inv k V
    ((E.hom.val.app (op V)).hom m)
  have h : (E.inv.val.app (op V)).hom ((E.hom.val.app (op V)).hom m) = m :=
    congrArg (fun f : L.over U ⟶ L.over U => (f.val.app (op V)).hom m) E.hom_inv_id
  exact h₁.trans (h₂.trans (congrArg (fun z : Γ(L, V.left) =>
    (k.val.app (op V)).hom z) h))

/-- Restoring an operator and expressing it in the same coframe returns that operator. -/
theorem framedOpenOperator_coframed {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (L : X.Modules) (U : X.Opens) (E : L.over U ≅ (unitModule X).over U)
    (φ : SchemeFrobeniusMap U.toScheme p) :
    framedOpenOperator base L U E (coframedOpenMap base L U E φ) = φ := by
  unfold framedOpenOperator coframedOpenMap
  apply (openOperatorEquiv C p base U).symm.injective
  rw [Equiv.symm_apply_apply]
  apply RelativeGlue.over_hom_ext (frobeniusRestriction C p base (unitModule X))
    (unitModule X) U
  intro V m
  let k := (openOperatorEquiv C p base U).symm φ
  have h₁ := twistedOverMap_comp_apply base (unitModule X) L (unitModule X) U E.inv
    (twistedOverMap base L (unitModule X) U E.hom ≫ k) V m
  have h₂ := twistedOverMap_comp_apply base L (unitModule X) (unitModule X) U E.hom k V
    ((E.inv.val.app (op V)).hom m)
  have h : (E.hom.val.app (op V)).hom ((E.inv.val.app (op V)).hom m) = m :=
    congrArg (fun f : (unitModule X).over U ⟶ (unitModule X).over U =>
      (f.val.app (op V)).hom m) E.inv_hom_id
  exact h₁.trans (h₂.trans (congrArg (fun z : Γ(X, V.left) =>
    (k.val.app (op V)).hom z) h))

end SchubertGeometry.ProjectiveCartier
