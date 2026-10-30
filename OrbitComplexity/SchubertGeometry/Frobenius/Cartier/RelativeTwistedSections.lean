import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedOperators
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Section coefficients for relative Cartier charts -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting FrobeniusSplitting.OperatorSheaf
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open RelativeGlue

open private indices line chart chartOpen relativeBase sourceLine relativeTrace unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

open private unitOf
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedFrame

open private sectionCoefficient sectionCoefficientValue
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights

open private sectionWeight
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeCartierOperator

private theorem module_triple_value {X : Scheme.{u}} {M N P Q : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (h : P ⟶ Q) (U : X.Opens)
    (a : M.val.obj (op U)) :
    ((f ≫ g ≫ h).val.app (op U)).hom a =
      (h.val.app (op U)).hom (((f ≫ g).val.app (op U)).hom a) := rfl

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

private def sectionProjection
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    unitLine (A := A) ⟶
      (Scheme.Modules.pushforward (chart A j)).obj (unitOf (Spec (.of (Polynomial A)))) :=
  m ≫ ProjectiveLine.projectiveInfinityFactor A (p - 1) ≫ projectiveCartierProjection A p j

private def sectionPolynomial
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    Polynomial A :=
  (Scheme.ΓSpecIso (.of (Polynomial A))).hom
    (((sectionProjection m j).val.app (op ⊤)).hom (1 : Γ(line A, ⊤)))

private theorem sectionCoefficient_pullback
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    (chart A j).isoOpensRange.hom.appTop
        ((chartOpen A j).topIso.inv (sectionCoefficientValue m j)) =
      (Scheme.ΓSpecIso (.of (Polynomial A))).inv (sectionPolynomial m j) := by
  let q : unitLine (A := A) ⟶
      (Scheme.Modules.pushforward (chart A j)).obj (unitOf (Spec (.of (Polynomial A)))) :=
    sectionProjection m j
  let U : (line A).Opens := chartOpen A j
  let T : Over U := Over.mk (𝟙 U)
  have hc : (q.over U ≫ (unitOverRangeIso (chart A j)).inv) =
      sectionCoefficient m j := by
    apply over_hom_ext (unitLine (A := A)) (unitLine (A := A)) U
    intro V a
    rfl
  have hv := congrArg (fun f => (f.val.app (op T)).hom (1 : Γ(line A, U))) hc
  have h := unit_range_coefficient (chart A j) q
  have hΓ := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso (.of (Polynomial A))).hom_inv_id
    ((q.val.app (op ⊤)).hom (1 : Γ(line A, ⊤)))
  have hleft := congrArg (fun c : Γ(line A, U) =>
    (chart A j).isoOpensRange.hom.appTop (U.topIso.inv c)) hv
  exact hleft.symm.trans (h.trans hΓ.symm)

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev basicChart (A : Type u) [CommRing A] (j : indices.{u}) : (line A).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule indices.{u} A) (MvPolynomial.X j)

private def insertedInfinity
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) :
    (ProjectiveLine.projectiveTransitionModule A (2 * (p - 1))).val.obj (op ⊤) :=
  ((m ≫ ProjectiveLine.projectiveInfinityFactor A (p - 1)).val.app (op ⊤)).hom
    (1 : Γ(line A, ⊤))

private theorem sectionWeight_projection
    (s : (ProjectiveLine.projectiveTransitionModule A (2 * (p - 1))).val.obj (op ⊤))
    (j : indices.{u}) :
    sectionWeight (p := p) s j = (Scheme.ΓSpecIso (.of (Polynomial A))).hom
      (((projectiveCartierProjection A p j).val.app (op ⊤)).hom s) := by
  rcases j with ⟨j⟩
  fin_cases j <;> rfl

private theorem insertedInfinity_coefficient
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    sectionWeight (p := p) (insertedInfinity m) j = sectionPolynomial m j := by
  have h := module_triple_value m (ProjectiveLine.projectiveInfinityFactor A (p - 1))
    (projectiveCartierProjection A p j) ⊤ (1 : Γ(line A, ⊤))
  exact (sectionWeight_projection (insertedInfinity m) j).trans
    (congrArg (Scheme.ΓSpecIso (.of (Polynomial A))).hom h).symm

private def auxiliaryOperator (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) :
    SchemeFrobeniusMap (line A) p :=
  relativeCartierOperator (K := K) ψ (insertedInfinity m)

private theorem auxiliaryOperator_chart (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    (auxiliaryOperator (K := K) ψ m).restrict (basicChart A j) =
      (((polynomialTraceOfOperator (K := K) ψ).weight (sectionPolynomial m j)).toSpec
        (expChar_pos K p)).pushforward (projectiveLinePolynomialIso A j).hom := by
  have h := relativeCartierOperator_chart (K := K) ψ (insertedInfinity m) j
  simpa only [auxiliaryOperator, insertedInfinity_coefficient] using h


end SchubertGeometry.ProjectiveCartier
