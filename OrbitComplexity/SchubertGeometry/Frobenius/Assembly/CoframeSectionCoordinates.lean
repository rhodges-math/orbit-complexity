import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPriorNormalization
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenCoframeOverlaps
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Section coefficients through an open chart

The coefficient of a global section in the range coframe returns the specified
chart coefficient under the chart isomorphism. All module and ring comparisons
are made before choosing any polynomial chart.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.OperatorSheaf

namespace SchubertGeometry.ProjectiveCartier

open private rangeSection rangeScalar rangeSection_smul from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFrameSections
open private rangeSection_pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordPriorNormalization
open private rangeScalarHom rangeCoordinateIso rangeCoordinate_retraction from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingCoordinateIso
open private generator_range from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.OpenCoframeOverlaps

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem rangeScalar_coordinate {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] (a : Γ(A, ⊤)) :
    j.isoOpensRange.hom.appTop (j.opensRange.topIso.inv (rangeScalar j a)) = a := by
  have hv : rangeScalarHom j = (rangeCoordinateIso j).inv := by
    apply (cancel_epi (rangeCoordinateIso j).hom).mp
    exact (rangeCoordinate_retraction j).trans (rangeCoordinateIso j).hom_inv_id.symm
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f ≫ (rangeCoordinateIso j).hom) hv) a
  exact h.trans (ConcreteCategory.congr_hom (rangeCoordinateIso j).inv_hom_id a)

private def chartCoefficientData {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) (s : unitModule X ⟶ L)
    (E : (Scheme.Modules.pullback j).obj L ≅ unitModule A) (a : Γ(A, ⊤)) : Prop :=
  let U := j.opensRange
  let c : Γ(X, U) := ((s.over U ≫ (coframeOverRange j L E).hom).val.app
    (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))
  j.isoOpensRange.hom.appTop (U.topIso.inv c) = a

/-- The coefficient of a section in a chart coframe is unchanged by passing
to the coframe on the open range and returning through the chart isomorphism. -/
theorem coframeRange_section_coefficient {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] (L : X.Modules) (s : unitModule X ⟶ L)
    (E : (Scheme.Modules.pullback j).obj L ≅ unitModule A) (a : Γ(A, ⊤))
    (hs : ((pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s) ≫ E.hom =
      globalSectionsSmul (unitModule A) a) : chartCoefficientData j L s E a := by
  let U := j.opensRange
  let F := coframeOverRange j L E
  let c : Γ(X, U) := ((s.over U ≫ F.hom).val.app (op (Over.mk (𝟙 U)))).hom
    (1 : Γ(X, U))
  let b : Γ(L, U) := coframeGenerator L U F
  have hsection := coframe_section_value ((Scheme.Modules.pullback j).obj L)
    ((pullbackObjUnitIso j).inv ≫ (Scheme.Modules.pullback j).map s) E a hs
  have hrange := (rangeSection_pullSection j L s).symm.trans
    ((congrArg (rangeSection j L) hsection).trans
      (rangeSection_smul j L a (E.inv.app ⊤ (1 : Γ(A, ⊤)))))
  have hgen : rangeSection j L (E.inv.app ⊤ (1 : Γ(A, ⊤))) = b :=
    (generator_range j L E).symm
  have hsec : L.presheaf.map U.leTop.op (s.app ⊤ (1 : Γ(X, ⊤))) =
      rangeScalar j a • b := hrange.trans (congrArg (fun z : Γ(L, U) =>
        rangeScalar j a • z) hgen)
  have hb : (F.hom.val.app (op (Over.mk (𝟙 U)))).hom b = (1 : Γ(X, U)) :=
    congrArg (fun f : (unitModule X).over U ⟶ (unitModule X).over U =>
      (f.val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))) F.inv_hom_id
  have hv : (s.val.app (op U)).hom (1 : Γ(X, U)) =
      L.presheaf.map U.leTop.op (s.app ⊤ (1 : Γ(X, ⊤))) := by
    have h := ConcreteCategory.congr_hom (s.val.naturality U.leTop.op)
      (1 : Γ(X, ⊤))
    change (s.val.app (op U)).hom (X.presheaf.map U.leTop.op (1 : Γ(X, ⊤))) = _ at h
    exact (congrArg (fun z : Γ(X, U) => (s.val.app (op U)).hom z)
      ((X.presheaf.map U.leTop.op).hom.map_one)).symm.trans h
  have hc : c = rangeScalar j a := by
    have h₁ := congrArg (fun z : Γ(L, U) =>
      (F.hom.val.app (op (Over.mk (𝟙 U)))).hom z) (hv.trans hsec)
    let v : Γ(L, U) →ₗ[Γ(X, U)] Γ(X, U) :=
      (F.hom.val.app (op (Over.mk (𝟙 U)))).hom
    have hb' : v b = 1 := hb
    have h₂ := v.map_smul (rangeScalar j a) b
    have h₃ : rangeScalar j a * v b = rangeScalar j a := by rw [hb', mul_one]
    exact h₁.trans (h₂.trans h₃)
  exact (congrArg (fun z : Γ(X, U) => j.isoOpensRange.hom.appTop (U.topIso.inv z)) hc).trans
    (rangeScalar_coordinate j a)

end SchubertGeometry.ProjectiveCartier
