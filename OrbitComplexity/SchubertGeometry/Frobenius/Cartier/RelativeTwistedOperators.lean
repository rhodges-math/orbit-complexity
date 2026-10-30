import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Relative Cartier chart maps as weighted operators -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting FrobeniusSplitting.OperatorSheaf
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open RelativeGlue

open private indices line chart chartOpen relativeBase sourceLine unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

open private twistModuleMap sectionCoefficientValue chart_precompose_weight
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

private theorem equiv_action_symm {S : Type*} {T : Type*}
    (e : S ≃ T) (w : S → S) (v : T → T) {x : S} {t : T}
    (hx : x = w (e.symm t)) (hw : ∀ y, e (w y) = v (e y)) : e x = v t :=
  (congrArg e hx).trans
    ((hw (e.symm t)).trans (congrArg v (e.apply_symm_apply t)))

private theorem chart_precompose_operator (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    openOperatorEquiv K p (relativeBase (K := K) (A := A)) (chartOpen A j)
        ((twistModuleMap (C := K) (q := p) (relativeBase (K := K) (A := A)) m).over (chartOpen A j)
          ≫
          relativeTwistedCartierChart (K := K) ψ j) =
      (((polynomialTraceOfOperator (K := K) ψ).toSpec (expChar_pos K p)).pushforward
        (chart A j).isoOpensRange.hom).inputWeight
          ((chartOpen A j).topIso.inv (sectionCoefficientValue m j)) := by
  let e : localOperators (sheafFrobenius K p (relativeBase (K := K) (A := A)))
      (chartOpen A j) ≃ SchemeFrobeniusMap (chartOpen A j).toScheme p :=
    openOperatorEquiv K p (relativeBase (K := K) (A := A)) (chartOpen A j)
  let w : localOperators (sheafFrobenius K p (relativeBase (K := K) (A := A)))
      (chartOpen A j) → localOperators
        (sheafFrobenius K p (relativeBase (K := K) (A := A))) (chartOpen A j) :=
    fun φ => sectionCoefficientValue m j • φ
  let v : SchemeFrobeniusMap (chartOpen A j).toScheme p →
      SchemeFrobeniusMap (chartOpen A j).toScheme p :=
    fun φ => φ.inputWeight ((chartOpen A j).topIso.inv (sectionCoefficientValue m j))
  let τ : SchemeFrobeniusMap (chartOpen A j).toScheme p :=
    ((polynomialTraceOfOperator (K := K) ψ).toSpec (expChar_pos K p)).pushforward
      (chart A j).isoOpensRange.hom
  exact equiv_action_symm e w v (t := τ) (chart_precompose_weight (K := K) ψ m j)
    (fun y => openOperatorEquiv_smul (C := K) (p := p)
      (base := relativeBase (K := K) (A := A)) (chartOpen A j)
      (sectionCoefficientValue m j) y)


end SchubertGeometry.ProjectiveCartier
