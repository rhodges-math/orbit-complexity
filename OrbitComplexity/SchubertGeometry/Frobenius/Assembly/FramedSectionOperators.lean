import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FramedOperatorMaps
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Inserting a section into a coframed local operator

The coefficient of the section in the specified coframe is the sole input
weight. The line-source morphism is retained before this insertion.
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

private theorem coframe_insert {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (L : X.Modules) (U : X.Opens) (E : L.over U ≅ (unitModule X).over U)
    (m : (unitModule X).over U ⟶ L.over U)
    (k : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U) :
    let c : Γ(X, U) := ((m ≫ E.hom).val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))
    twistedOverMap base (unitModule X) L U m ≫ k =
      c • (show localOperators (sheafFrobenius C p base) U from
        twistedOverMap base (unitModule X) L U E.inv ≫ k) := by
  let c : Γ(X, U) := ((m ≫ E.hom).val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))
  apply RelativeGlue.over_hom_ext (frobeniusRestriction C p base (unitModule X))
    (unitModule X) U
  intro V a₀
  let a : Γ(X, V.left) := a₀
  have h₁ := twistedOverMap_comp_apply base (unitModule X) L (unitModule X) U m k V a
  have hc := RelativeGlue.unitOver_map_value U (m ≫ E.hom) V a
  have hc' : (E.hom.val.app (op V)).hom ((m.val.app (op V)).hom a) =
      X.presheaf.map V.hom.op c * a := hc
  have hi : (E.inv.val.app (op V)).hom
      ((E.hom.val.app (op V)).hom ((m.val.app (op V)).hom a)) =
      (m.val.app (op V)).hom a :=
    congrArg (fun f : L.over U ⟶ L.over U =>
      (f.val.app (op V)).hom ((m.val.app (op V)).hom a)) E.hom_inv_id
  have hm : (m.val.app (op V)).hom a =
      (E.inv.val.app (op V)).hom (X.presheaf.map V.hom.op c * a) :=
    hi.symm.trans (congrArg (fun z : Γ(X, V.left) => (E.inv.val.app (op V)).hom z) hc')
  have h₂ := inputModule_apply (sheafFrobenius C p base) U c
    (twistedOverMap base (unitModule X) L U E.inv ≫ k) V a
  have h₃ := twistedOverMap_comp_apply base (unitModule X) L (unitModule X) U E.inv k V
    (X.presheaf.map V.hom.op c * a)
  exact h₁.trans ((congrArg (fun z : Γ(L, V.left) =>
    (k.val.app (op V)).hom z) hm).trans (h₃.symm.trans h₂.symm))

/-- Inserting a local section weights the raw coframed operator by precisely
the coefficient of that section in the same coframe. -/
theorem coframeInsertion_operator {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (L : X.Modules) (U : X.Opens) (E : L.over U ≅ (unitModule X).over U)
    (m : (unitModule X).over U ⟶ L.over U)
    (k : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U) :
    let c : Γ(X, U) := ((m ≫ E.hom).val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))
    openOperatorEquiv C p base U
        (twistedOverMap base (unitModule X) L U m ≫ k) =
      (framedOpenOperator base L U E k).inputWeight (U.topIso.inv c) := by
  let c : Γ(X, U) := ((m ≫ E.hom).val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))
  have h := congrArg (openOperatorEquiv C p base U) (coframe_insert base L U E m k)
  exact h.trans (openOperatorEquiv_smul C p base U c
    (twistedOverMap base (unitModule X) L U E.inv ≫ k))

end SchubertGeometry.ProjectiveCartier
