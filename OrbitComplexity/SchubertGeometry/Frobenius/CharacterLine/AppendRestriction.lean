import OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Restriction maps for the two append charts -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
noncomputable section
universe u
namespace SchubertGeometry.CharacterLine
open private affine overlap line chart leftMap rightMap overlapMap overlapMap_right
  transitionSection from
  OrbitComplexity.SchubertGeometry.IntegralProjectiveLine.Transition

/-- The restriction from a chart to a specified overlap map. -/
private def leftRestrictionValue {P Q L : Scheme.{u}} (c : P ⟶ L) (f : Q ⟶ P) :=
  (pushforward c).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
    (pushforwardComp f c).hom.app (SheafOfModules.unit Q.ringCatSheaf)

/-- The restriction with its target identified by a scheme-map equality. -/
private def rightRestrictionValue {P Q L : Scheme.{u}} (c : P ⟶ L) (f : Q ⟶ P)
    (o : Q ⟶ L) (h : f ≫ c = o) :=
  (pushforward c).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
    (pushforwardComp f c).hom.app (SheafOfModules.unit Q.ringCatSheaf) ≫
    (pushforwardCongr h).hom.app (SheafOfModules.unit Q.ringCatSheaf)

/-- The restriction followed by multiplication by the transition section. -/
private def twistedRestrictionValue {P Q L : Scheme.{u}} (c : P ⟶ L) (f : Q ⟶ P)
    (o : Q ⟶ L) (h : f ≫ c = o) (v : Γ(Q, ⊤)) :=
  rightRestrictionValue c f o h ≫ (pushforward o).map
    (globalSectionsSmul (SheafOfModules.unit Q.ringCatSheaf) v)

variable (R : Type u) [CommRing R]

/-- The stored left restriction has the generic chart-restriction construction. -/
private theorem storedLeftDefinition : HEq (ProjectiveLine.leftRestriction R)
    (leftRestrictionValue (P := affine R) (Q := overlap R) (L := line R)
      (chart R ⟨0⟩) (leftMap R)) := by
  rfl

/-- The stored right restriction uses the specified overlap-map equality. -/
private theorem storedRightDefinition : HEq (ProjectiveLine.rightRestriction R)
    (rightRestrictionValue (P := affine R) (Q := overlap R) (L := line R)
      (chart R ⟨1⟩) (rightMap R) (overlapMap R) (overlapMap_right R)) := by
  rfl

/-- The stored twisted restriction multiplies by its transition section. -/
private theorem storedTwistedDefinition (d : ℕ) : HEq (ProjectiveLine.twistedRestriction R d)
    (twistedRestrictionValue (P := affine R) (Q := overlap R) (L := line R)
      (chart R ⟨1⟩) (rightMap R) (overlapMap R) (overlapMap_right R)
      (transitionSection R d)) := by
  rfl

end SchubertGeometry.CharacterLine
