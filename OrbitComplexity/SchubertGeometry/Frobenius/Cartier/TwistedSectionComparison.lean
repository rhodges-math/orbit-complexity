import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.TwistedPriorOperator
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Sections and Frobenius-restricted module maps

A map from the unit module is determined by the image of one. Naturality of that
image compares insertion of its global section with precomposition by the same
map after Frobenius restriction.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting

universe u

namespace SchubertGeometry.ProjectiveCartier

open RelativeGlue

open private twistModuleMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights

variable {C : Type u} [CommRing C] {p : ℕ} [ExpChar C p]
variable {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (L : X.Modules)

private theorem unitSection_restrict
    (m : SheafOfModules.unit X.ringCatSheaf ⟶ L) (U : X.Opens) :
    L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) =
      (m.val.app (op U)).hom (1 : Γ(X, U)) := by
  have h := ConcreteCategory.congr_hom
    (m.val.naturality (homOfLE (le_top : U ≤ ⊤)).op) (1 : Γ(X, ⊤))
  change (m.val.app (op U)).hom
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(X, ⊤))) =
    L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) at h
  rw [map_one] at h
  exact h.symm

private theorem twist_precompose_value
    (Θ : frobeniusRestriction C p base L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (m : SheafOfModules.unit X.ringCatSheaf ⟶ L) (Φ : SchemeFrobeniusMap X p)
    (h : twistModuleMap base m ≫ Θ = schemeOperatorHom base Φ)
    (U : X.Opens) (a : Γ(X, U)) :
    (Θ.val.app (op U)).hom ((m.val.app (op U)).hom a) = Φ.onOpen U a := by
  exact congrArg
    (fun f : frobeniusRestriction C p base (SheafOfModules.unit X.ringCatSheaf) ⟶
        SheafOfModules.unit X.ringCatSheaf => (f.val.app (op U)).hom a) h

/-- Inserting the image of one of a unit-module map gives the scheme operator
identified by its Frobenius-restricted precomposition. -/
theorem twistedSectionOperator_eq
    (Θ : frobeniusRestriction C p base L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (m : SheafOfModules.unit X.ringCatSheaf ⟶ L) (Φ : SchemeFrobeniusMap X p)
    (h : twistModuleMap base m ≫ Θ = schemeOperatorHom base Φ) :
    twistedSectionOperator base L Θ ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) = Φ := by
  apply SchemeFrobeniusMap.ext
  intro U a
  change (Θ.val.app (op U)).hom
      ((L.smul a).hom (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        ((m.val.app (op ⊤)).hom (1 : Γ(X, ⊤))))) = Φ.onOpen U a
  rw [unitSection_restrict L m U]
  have hm : (L.smul a).hom ((m.val.app (op U)).hom (1 : Γ(X, U))) =
      (m.val.app (op U)).hom a := by
    have hlin : (m.val.app (op U)).hom (a * 1) =
        (L.smul a).hom ((m.val.app (op U)).hom (1 : Γ(X, U))) :=
      (m.val.app (op U)).hom.map_smul a (1 : Γ(X, U))
    exact hlin.symm.trans
      (congrArg (fun x : Γ(X, U) => (m.val.app (op U)).hom x) (mul_one a))
  rw [hm]
  exact twist_precompose_value base L Θ m Φ h U a

end SchubertGeometry.ProjectiveCartier
