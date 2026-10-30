import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedFrame
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedGluingSupport
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.GlobalCoordinates
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Input weights for relative Cartier charts -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting FrobeniusSplitting.OperatorSheaf
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open RelativeGlue

open private indices line chart chartOpen relativeBase sourceLine relativeTrace
  infinityCoefficient infinityCoefficient_value unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

private def twistModuleComponent {C : Type u} [CommRing C] {q : ℕ} [ExpChar C q]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) {M N : X.Modules} (m : M ⟶ N)
    (V : X.Opensᵒᵖ) :
    (frobeniusRestriction C q base M).val.obj V ⟶
      (frobeniusRestriction C q base N).val.obj V :=
  { hom' :=
      { toFun := fun a => (m.val.app V).hom a
        map_add' := fun a b => (m.val.app V).hom.map_add a b
        map_smul' := fun r a => by
          let c : Γ(X, V.unop) := r
          exact (m.val.app V).hom.map_smul (c ^ q) a } }

private def twistModuleMap {C : Type u} [CommRing C] {q : ℕ} [ExpChar C q]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) {M N : X.Modules} (m : M ⟶ N) :
    frobeniusRestriction C q base M ⟶ frobeniusRestriction C q base N where
  val :=
    { app := fun V => twistModuleComponent (q := q) base m V
      naturality := fun {V W} f => by
        ext a
        exact ConcreteCategory.congr_hom (m.val.naturality f) a }

private theorem twistModuleMap_value {C : Type u} [CommRing C] {q : ℕ} [ExpChar C q]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) {M N : X.Modules} (m : M ⟶ N)
    (U : X.Opens) (V : Over U) (a : M.val.obj (op V.left)) :
    ((((twistModuleMap (q := q) base m).over U).val.app (op V)).hom a) =
      (m.val.app (op V.left)).hom a := rfl

private def sectionCoefficient
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    (unitLine (A := A)).over (chartOpen A j) ⟶
      (unitLine (A := A)).over (chartOpen A j) :=
  m.over (chartOpen A j) ≫ infinityCoefficient (A := A) (p := p) j

private def sectionCoefficientValue
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    Γ(line A, chartOpen A j) :=
  ((sectionCoefficient m j).val.app (op (Over.mk (𝟙 (chartOpen A j))))).hom
    (1 : Γ(line A, chartOpen A j))

private theorem overComp_value {X : Scheme.{u}} (M N P : X.Modules) (U : X.Opens)
    (f : M.over U ⟶ N.over U) (g : N.over U ⟶ P.over U) (V : Over U)
    (a : M.val.obj (op V.left)) :
    ((f ≫ g).val.app (op V)).hom a =
      (g.val.app (op V)).hom ((f.val.app (op V)).hom a) := rfl

private theorem coefficientValue_eq
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    sectionCoefficientValue m j =
      ((m.over (chartOpen A j) ≫ infinityCoefficient (A := A) (p := p) j).val.app
        (op (Over.mk (𝟙 (chartOpen A j))))).hom (1 : Γ(line A, chartOpen A j)) := rfl

private theorem chart_precompose_weight_value (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u})
    (V : Over (chartOpen A j)) (a : Γ(line A, V.left)) :
    (show Γ(line A, V.left) from
      (((twistModuleMap (C := K) (q := p) (relativeBase (K := K) (A := A)) m).over
        (chartOpen A j) ≫ relativeTwistedCartierChart (K := K) ψ j).val.app (op V)).hom a) =
      (show Γ(line A, V.left) from
        ((sectionCoefficientValue m j • relativeTrace (K := K) ψ j).val.app (op V)).hom a) := by
  have hcomp := overComp_value
    (frobeniusRestriction K p (relativeBase (K := K) (A := A)) (unitLine (A := A)))
    (frobeniusRestriction K p (relativeBase (K := K) (A := A))
      (sourceLine (A := A) (p := p)))
    (unitLine (A := A)) (chartOpen A j)
    ((twistModuleMap (C := K) (q := p) (relativeBase (K := K) (A := A)) m).over (chartOpen A j))
    (relativeTwistedCartierChart (K := K) ψ j) V a
  have hmap := congrArg
    (fun t : (sourceLine (A := A) (p := p)).val.obj (op V.left) =>
      ((relativeTwistedCartierChart (K := K) ψ j).val.app (op V)).hom t)
    (twistModuleMap_value (C := K) (q := p) (relativeBase (K := K) (A := A))
      m (chartOpen A j) V a)
  have hc := relativeTwistedCartierChart_apply (K := K) ψ j V
    ((m.val.app (op V.left)).hom a)
  have hm := precompose_trace_value K p (relativeBase (K := K) (A := A))
    (sourceLine (A := A) (p := p)) (chartOpen A j) m
    (infinityCoefficient (A := A) (p := p) j) (relativeTrace (K := K) ψ j) V a
  have hweight := congrArg
    (fun c : Γ(line A, chartOpen A j) =>
      ((c • relativeTrace (K := K) ψ j).val.app (op V)).hom a)
    (coefficientValue_eq m j)
  exact hcomp.trans (hmap.trans (hc.trans (hm.trans hweight.symm)))

private theorem chart_precompose_weight (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    ((twistModuleMap (C := K) (q := p) (relativeBase (K := K) (A := A)) m).over (chartOpen A j) ≫
      relativeTwistedCartierChart (K := K) ψ j) =
        sectionCoefficientValue m j • relativeTrace (K := K) ψ j := by
  ext V a
  exact chart_precompose_weight_value (K := K) ψ m j V.unop a


end SchubertGeometry.ProjectiveCartier
