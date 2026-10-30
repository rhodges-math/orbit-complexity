import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts
import OrbitComplexity.GroupActions.Modules.UnitCoherence
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Normalization in a prior line frame

Evaluating a twisted Cartier functional on a global section determines its
normalization in every affine line frame. Open restriction and pullback are
compared before passing to chart coordinates.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules FrobeniusSplitting
namespace SchubertGeometry.ProjectiveCartier
universe u

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

open private chartCoordinateIso chartTwistedOperator
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorCharts

/-- Pulling back a section and then comparing with open restriction agrees
with restricting the same section through the structure-sheaf comparison. -/
theorem pullSection_restrictFunctor {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (L : Y.Modules) (s : unitModule Y ⟶ L) :
    (pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s ≫
        (restrictFunctorIsoPullback j).inv.app L =
      (restrictUnitIso j).inv ≫ (restrictFunctor j).map s := by
  have hUnit :
      ((restrictFunctorIsoPullback j).app (SheafOfModules.unit Y.ringCatSheaf)) ≪≫
        pullbackObjUnitIso j = restrictUnitIso j :=
    Iso.ext (GroupActions.restrictPullback_unit j)
  have hInv : (pullbackObjUnitIso j).inv ≫
      (restrictFunctorIsoPullback j).inv.app (SheafOfModules.unit Y.ringCatSheaf) =
        (restrictUnitIso j).inv := congrArg Iso.inv hUnit
  rw [(restrictFunctorIsoPullback j).inv.naturality, ← Category.assoc]
  exact congrArg (fun t : unitModule X ⟶ (restrictFunctor j).obj (unitModule Y) =>
    t ≫ (restrictFunctor j).map s) hInv

/-- The section obtained by transporting a pulled-back global section to the
image open is the restriction of that original global section. -/
theorem imageSection_pullSection {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (L : Y.Modules) (s : unitModule Y ⟶ L) :
    (L.restrictAppIso j ⊤).hom
      ((((restrictFunctorIsoPullback j).inv.app L).val.app (op ⊤)).hom
        (((((pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s).val.app
          (op ⊤)).hom) (1 : Γ(X, ⊤)))) =
      L.presheaf.map (homOfLE (le_top : j ''ᵁ (⊤ : X.Opens) ≤ ⊤)).op
        ((s.val.app (op ⊤)).hom (1 : Γ(Y, ⊤))) := by
  have h := congrArg
    (fun f : unitModule X ⟶ (restrictFunctor j).obj L =>
      (f.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) (pullSection_restrictFunctor j L s)
  have hUnit : (((restrictUnitIso j).inv.val.app (op ⊤)).hom) (1 : Γ(X, ⊤)) =
      (1 : Γ(Y, j ''ᵁ (⊤ : X.Opens))) := by
    change (j.appIso ⊤).inv (1 : Γ(X, ⊤)) = 1
    exact map_one _
  have hn := ConcreteCategory.congr_hom
    (s.mapPresheaf.naturality
      (homOfLE (le_top : j ''ᵁ (⊤ : X.Opens) ≤ ⊤)).op) (1 : Γ(Y, ⊤))
  change (s.val.app (op (j ''ᵁ (⊤ : X.Opens)))).hom
      ((Y.presheaf.map (homOfLE (le_top : j ''ᵁ (⊤ : X.Opens) ≤ ⊤)).op).hom
        (1 : Γ(Y, ⊤))) =
    L.presheaf.map (homOfLE (le_top : j ''ᵁ (⊤ : X.Opens) ≤ ⊤)).op
      ((s.val.app (op ⊤)).hom (1 : Γ(Y, ⊤))) at hn
  have hOne := (Y.presheaf.map
    (homOfLE (le_top : j ''ᵁ (⊤ : X.Opens) ≤ ⊤)).op).hom.map_one
  rw [hOne] at hn
  change (((restrictFunctorIsoPullback j).inv.app L).val.app (op ⊤)).hom
      (((((pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s).val.app
        (op ⊤)).hom) (1 : Γ(X, ⊤))) = _
  change (((restrictFunctorIsoPullback j).inv.app L).val.app (op ⊤)).hom
      (((((pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s).val.app
        (op ⊤)).hom) (1 : Γ(X, ⊤))) =
    ((restrictFunctor j).map s).app ⊤
      ((((restrictUnitIso j).inv.val.app (op ⊤)).hom) (1 : Γ(X, ⊤))) at h
  exact h.trans (by rw [hUnit]; exact hn)

/-- A twisted functional normalized on one global section is normalized on
that section's coefficient in every line frame. -/
theorem twistedFrameOperator_normalized {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ unitModule X)
    (s : Γ(L, ⊤)) (hnorm : Θ.app ⊤ s = (1 : Γ(X, ⊤)))
    (U : X.Opens) (e : Γ(L, U)) (f : Γ(X, U))
    (hs : L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = f • e) :
    twistedFrameOperator base L Θ U e f = 1 := by
  have hn := ConcreteCategory.congr_hom
    (Θ.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op) s
  change Θ.app U (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) =
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (Θ.app ⊤ s) at hn
  change Θ.app U (f • e) = (1 : Γ(X, U))
  rw [← hs]
  exact hn.trans (by rw [hnorm]; exact (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.map_one)

/-- The normalized prior coefficient is transported to its original affine
ring by the chart coordinate isomorphism. -/
theorem chartTwistedOperator_normalized {C A : Type u} [CommRing C] [CommRing A]
    {p : ℕ} [ExpChar C p] {Y : Scheme.{u}}
    (base : Y ⟶ Spec (.of C)) (L : Y.Modules)
    (Θ : frobeniusRestriction C p base L ⟶ unitModule Y)
    (s : Γ(L, ⊤)) (hnorm : Θ.app ⊤ s = (1 : Γ(Y, ⊤)))
    (j : Spec (.of A) ⟶ Y) [IsOpenImmersion j]
    (e : Γ(L, j.opensRange)) (f : Γ(Y, j.opensRange)) (a : A)
    (hs : L.presheaf.map (homOfLE (le_top : j.opensRange ≤ ⊤)).op s = f • e)
    (ha : (chartCoordinateIso j).hom f = a) :
    chartTwistedOperator base L Θ j e a = 1 := by
  let E := (chartCoordinateIso j).commRingCatIsoToRingEquiv
  have hInv : E.symm a = f := by
    apply E.injective
    exact (E.apply_symm_apply a).trans ha.symm
  have h := twistedFrameOperator_normalized base L Θ s hnorm j.opensRange e f hs
  change E (twistedFrameOperator base L Θ j.opensRange e (E.symm a)) = 1
  rw [hInv, h, map_one]

end SchubertGeometry.ProjectiveCartier
