import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FramedPushforward
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.OpenSectionOperators
import OrbitComplexity.FrobeniusSplitting.Splittings.Pushforward
import OrbitComplexity.FrobeniusSplitting.Splittings.OperatorNormalization
import OrbitComplexity.FrobeniusSplitting.Splittings.Restriction

/-! # Pushing forward a section-inserted splitting

The global twisted operator determines the restriction of the splitting.
Coframe evaluation then describes its pushforward as a weighted operator.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite FrobeniusSplitting
open FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private twistedOverMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem restrict_operator {X : Scheme.{u}} {p : ℕ}
    (S : SchemeSplitting X p) (U : X.Opens) :
    (S.restrict U).toOperator = S.toOperator.restrict U := by
  apply SchemeFrobeniusMap.ext
  intro V a
  rfl

private theorem pushforward_operator {X Y : Scheme.{u}} {p : ℕ}
    (S : SchemeSplitting X p) (f : X ⟶ Y) [IsIso f.c] :
    (S.pushforward f).toOperator = S.toOperator.pushforward f := by
  apply SchemeFrobeniusMap.ext
  intro V a
  rfl

/-- The pushforward of a section-inserted splitting is its coframed raw pushforward
weighted by the section coefficient. -/
theorem twistedSplitting_pushforward {C : Type u} [CommRing C]
    {p : ℕ} [ExpChar C p] {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ unitModule X)
    (m : unitModule X ⟶ L) (S : SchemeSplitting X p)
    (hS : S.toOperator = twistedSectionOperator base L Θ
      ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤))))
    (U : X.Opens) (E : L.over U ≅ (unitModule X).over U)
    (f : U.toScheme ⟶ Y) [IsIso f.c] (c : Γ(Y, ⊤))
    (hc : U.topIso.inv
      (((m.over U ≫ E.hom).val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))) =
        f.appTop c) :
    ((S.restrict U).pushforward f).toOperator =
      ((framedOpenOperator base L U E (Θ.over U)).pushforward f).inputWeight c := by
  have hU : (S.restrict U).toOperator = openOperatorEquiv C p base U
      (twistedOverMap base (unitModule X) L U (m.over U) ≫ Θ.over U) := by
    calc
      (S.restrict U).toOperator = S.toOperator.restrict U := restrict_operator S U
      _ = (twistedSectionOperator base L Θ
          ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤)))).restrict U :=
        congrArg (fun q : SchemeFrobeniusMap X p => q.restrict U) hS
      _ = _ := (twistedSectionOperator_onOpen base L Θ m U).symm
  calc
    ((S.restrict U).pushforward f).toOperator =
        (S.restrict U).toOperator.pushforward f := pushforward_operator (S.restrict U) f
    _ = (openOperatorEquiv C p base U
        (twistedOverMap base (unitModule X) L U (m.over U) ≫ Θ.over U)).pushforward f :=
      congrArg (fun q : SchemeFrobeniusMap U.toScheme p => q.pushforward f) hU
    _ = _ := coframeInsertion_pushforward base L U E (m.over U) (Θ.over U) f c hc

end SchubertGeometry.ProjectiveCartier
