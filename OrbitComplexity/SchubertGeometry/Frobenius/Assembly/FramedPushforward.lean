import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FramedSectionOperators

/-! # Direct images of Cartier operators in a coframe -/

open AlgebraicGeometry CategoryTheory Opposite
open FrobeniusSplitting.OperatorSheaf

set_option autoImplicit false
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open FrobeniusSplitting

open private twistedOverMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem pushforward_weight {X Y : Scheme.{u}} {p : ℕ}
    (φ : SchemeFrobeniusMap X p) (f : X ⟶ Y) [IsIso f.c]
    (c : Γ(Y, ⊤)) :
    (φ.inputWeight (f.appTop c)).pushforward f =
      (φ.pushforward f).inputWeight c := by
  apply SchemeFrobeniusMap.ext
  intro U s
  apply (asIso (f.app U)).commRingCatIsoToRingEquiv.injective
  change f.app U _ = f.app U _
  rw [SchemeFrobeniusMap.pushforward_app, SchemeFrobeniusMap.inputWeight_apply,
    SchemeFrobeniusMap.inputWeight_apply, SchemeFrobeniusMap.pushforward_app]
  have hc : X.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop c) =
      f.app U (Y.presheaf.map U.leTop.op c) :=
    (congrArg (fun k : Γ(Y, ⊤) ⟶ Γ(X, f ⁻¹ᵁ U) => k c)
      (f.naturality U.leTop.op)).symm
  rw [hc, (f.app U).hom.map_mul]

/-- A section inserted into a Cartier map descends with its coefficient in the same coframe. -/
theorem coframeInsertion_pushforward {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X Y : Scheme.{u}} (base : X ⟶ Spec (.of C))
    (L : X.Modules) (U : X.Opens) (E : L.over U ≅ (unitModule X).over U)
    (m : (unitModule X).over U ⟶ L.over U)
    (k : (frobeniusRestriction C p base L).over U ⟶ (unitModule X).over U)
    (f : U.toScheme ⟶ Y) [IsIso f.c] (c : Γ(Y, ⊤))
    (hc : U.topIso.inv
      (((m ≫ E.hom).val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))) =
        f.appTop c) :
    (openOperatorEquiv C p base U
      (twistedOverMap base (unitModule X) L U m ≫ k)).pushforward f =
        ((framedOpenOperator base L U E k).pushforward f).inputWeight c := by
  rw [coframeInsertion_operator]
  change ((framedOpenOperator base L U E k).inputWeight
    (U.topIso.inv
      (((m ≫ E.hom).val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))))).pushforward f = _
  rw [hc]
  exact pushforward_weight (framedOpenOperator base L U E k) f c

end SchubertGeometry.ProjectiveCartier
