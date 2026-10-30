import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedSectionComparison
import OrbitComplexity.FrobeniusSplitting.Cartier.OpenOperators
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Restricting a section inserted into a twisted operator

Precomposition with a section on an open subscheme gives the restriction of
the globally inserted operator. The comparison takes place over an arbitrary
scheme, with the module and its restriction fixed throughout.
-/

set_option autoImplicit false

noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open FrobeniusSplitting FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private twistedOverMap twistedOverMap_comp_apply from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
open private unitSection_restrict from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedSectionComparison
open private imageIn from OrbitComplexity.FrobeniusSplitting.Cartier.OpenOperators

private theorem unit_section_apply {X : Scheme.{u}} (L : X.Modules)
    (m : SheafOfModules.unit X.ringCatSheaf ⟶ L) (U : X.Opens) (a : Γ(X, U)) :
    (Scheme.Modules.Hom.app m U).hom a =
      a • (Scheme.Modules.Hom.app m U).hom (1 : Γ(X, U)) := by
  let f : Γ(X, U) →ₗ[Γ(X, U)] Γ(L, U) := (m.val.app (op U)).hom
  change f a = a • f (1 : Γ(X, U))
  simpa only [smul_eq_mul, mul_one] using f.map_smul a (1 : Γ(X, U))

/-- Inserting a global section into the raw twisted map over an open gives
the restriction of the global section-inserted structure-sheaf operator. -/
theorem twistedSectionOperator_onOpen {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (L : X.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (m : SheafOfModules.unit X.ringCatSheaf ⟶ L) (U : X.Opens) :
    openOperatorEquiv C p base U
      (twistedOverMap base (SheafOfModules.unit X.ringCatSheaf) L U (m.over U) ≫
        Θ.over U) =
      (twistedSectionOperator base L Θ
        ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))).restrict U := by
  apply SchemeFrobeniusMap.ext
  intro V a
  refine (openOperatorEquiv_apply C p base U _ V a).trans ?_
  refine (twistedOverMap_comp_apply base (SheafOfModules.unit X.ringCatSheaf)
    L (SheafOfModules.unit X.ringCatSheaf) U (m.over U) (Θ.over U)
      (imageIn U V) a).trans ?_
  let W : X.Opens := (imageIn U V).left
  let x : Γ(X, W) := a
  change (Θ.val.app (op W)).hom ((Scheme.Modules.Hom.app m W).hom x) =
    (Θ.val.app (op W)).hom
      (x • L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤))))
  exact congrArg (fun z : Γ(L, W) => (Θ.val.app (op W)).hom z)
    ((unit_section_apply L m W x).trans
      (congrArg (fun z : Γ(L, W) => x • z) (unitSection_restrict L m W).symm))

end SchubertGeometry.ProjectiveCartier
