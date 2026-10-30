import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections
import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedPullback
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Comparing relative Cartier chart maps with global operators -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting FrobeniusSplitting.OperatorSheaf
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open RelativeGlue

open private indices line chart chartOpen relativeBase sourceLine relativeTrace unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

open private twistModuleMap sectionCoefficientValue chart_precompose_weight
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedWeights

open private sectionPolynomial sectionCoefficient_pullback basicChart
  auxiliaryOperator auxiliaryOperator_chart
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections

open private pushforward_openPullback openPullback_injective chart_openPullback
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedPullback

/-! The maps compared below are typed through `frobeniusRestriction`, while
`openOperatorEquiv` takes `localOperators`. The two source modules agree only by
unfolding, and on the projective line the kernel then computes in its homogeneous
localizations. The four lemmas below make that identification once, over an arbitrary
scheme, so that the comparison on the line matches terms syntactically. -/

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: frobeniusUnit_hom_ext"

/-- Two maps from the Frobenius restriction of the unit agree when their local
operators agree after pullback along an isomorphism onto the open set. -/
private theorem frobeniusUnit_hom_ext {C : Type u} [CommRing C] {q : ℕ} [ExpChar C q]
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens) (e : Y ≅ U.toScheme)
    {f g : (frobeniusRestriction C q base (SheafOfModules.unit X.ringCatSheaf)).over U ⟶
      (SheafOfModules.unit X.ringCatSheaf).over U}
    (h : (openOperatorEquiv C q base U f).openPullback e.hom =
      (openOperatorEquiv C q base U g).openPullback e.hom) : f = g :=
  (openOperatorEquiv C q base U).injective (openPullback_injective e h)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: frobeniusUnit_operator_smul"

/-- A map from the Frobenius restriction of the unit that equals a section times a local
operator has that operator, weighted by the section, as its scheme operator. -/
private theorem frobeniusUnit_operator_smul {C : Type u} [CommRing C] {q : ℕ} [ExpChar C q]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens)
    {f : (frobeniusRestriction C q base (SheafOfModules.unit X.ringCatSheaf)).over U ⟶
      (SheafOfModules.unit X.ringCatSheaf).over U}
    (r : Γ(X, U)) (τ : localOperators (sheafFrobenius C q base) U) (h : f = r • τ) :
    openOperatorEquiv C q base U f =
      (openOperatorEquiv C q base U τ).inputWeight (U.topIso.inv r) :=
  (congrArg (openOperatorEquiv C q base U) h).trans
    (openOperatorEquiv_smul (C := C) (p := q) (base := base) U r τ)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: frobeniusUnit_schemeOperator"

/-- `schemeOperatorHom_over`, with the restricted map typed through the Frobenius
restriction of the unit. -/
private theorem frobeniusUnit_schemeOperator {C : Type u} [CommRing C] {q : ℕ} [ExpChar C q]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of C)) (φ : SchemeFrobeniusMap X q) (U : X.Opens) :
    openOperatorEquiv C q base U
        ((schemeOperatorHom base φ).over U :
          (frobeniusRestriction C q base (SheafOfModules.unit X.ringCatSheaf)).over U ⟶
            (SheafOfModules.unit X.ringCatSheaf).over U) =
      φ.restrict U :=
  schemeOperatorHom_over base φ U

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: frobeniusUnit_eq_schemeOperator"

/-- A map from the Frobenius restriction of the unit equals the restriction of the map of a
scheme operator `Φ` when it is a section `r` times a local operator `τ`, and the operator of
`τ`, weighted by `r`, agrees with `Φ` after pullback along an isomorphism onto the open set. -/
private theorem frobeniusUnit_eq_schemeOperator {C : Type u} [CommRing C] {q : ℕ}
    [ExpChar C q] {X Y : Scheme.{u}} (base : X ⟶ Spec (.of C)) (U : X.Opens)
    (e : Y ≅ U.toScheme)
    {f : (frobeniusRestriction C q base (SheafOfModules.unit X.ringCatSheaf)).over U ⟶
      (SheafOfModules.unit X.ringCatSheaf).over U}
    (r : Γ(X, U)) (τ : localOperators (sheafFrobenius C q base) U)
    {σ : SchemeFrobeniusMap U.toScheme q} (Φ : SchemeFrobeniusMap X q)
    (hf : f = r • τ) (hτ : openOperatorEquiv C q base U τ = σ)
    (hσ : (σ.inputWeight (U.topIso.inv r)).openPullback e.hom =
      (Φ.restrict U).openPullback e.hom) :
    f = (schemeOperatorHom base Φ).over U := by
  apply frobeniusUnit_hom_ext base U e
  have hleft : openOperatorEquiv C q base U f = σ.inputWeight (U.topIso.inv r) :=
    (frobeniusUnit_operator_smul base U r τ hf).trans
      (congrArg (fun φ : SchemeFrobeniusMap U.toScheme q => φ.inputWeight (U.topIso.inv r)) hτ)
  rw [hleft, frobeniusUnit_schemeOperator base Φ U]
  exact hσ

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: relativeTrace_operator"

private theorem relativeTrace_operator (ψ : FrobeniusLinearMap A p) (j : indices.{u}) :
    openOperatorEquiv K p (relativeBase (K := K) (A := A)) (chartOpen A j)
        (relativeTrace (K := K) ψ j) =
      ((polynomialTraceOfOperator (K := K) ψ).toSpec (expChar_pos K p)).pushforward
        (chart A j).isoOpensRange.hom :=
  Equiv.apply_symm_apply _ _

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: pullback_eq_of_hom_eq"

private theorem pullback_eq_of_hom_eq {X Y : Scheme.{u}}
    (φ : SchemeFrobeniusMap Y p) {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    φ.openPullback f = φ.openPullback g := by
  cases h
  rfl

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: auxiliaryOperator_pullback"

private theorem auxiliaryOperator_pullback (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    (auxiliaryOperator (K := K) ψ m).openPullback (chart A j) =
      ((polynomialTraceOfOperator (K := K) ψ).weight (sectionPolynomial m j)).toSpec
        (expChar_pos K p) := by
  let Φ : SchemeFrobeniusMap (line A) p := auxiliaryOperator (K := K) ψ m
  have hj : chart A j =
      (projectiveLinePolynomialIso A j).hom ≫ (basicChart A j).ι := rfl
  exact (pullback_eq_of_hom_eq Φ hj).trans
    (chart_openPullback (basicChart A j) (projectiveLinePolynomialIso A j)
      Φ _ (auxiliaryOperator_chart (K := K) ψ m j))

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: weighted_pushforward_pullback"

private theorem weighted_pushforward_pullback {X Y : Scheme.{u}} (e : X ≅ Y)
    (τ : SchemeFrobeniusMap X p) (c : Γ(Y, ⊤)) :
    ((τ.pushforward e.hom).inputWeight c).openPullback e.hom =
      τ.inputWeight (e.hom.appTop c) := by
  have hweight := SchemeFrobeniusMap.openPullback_inputWeight
    (τ.pushforward e.hom) e.hom c
  have hcancel := congrArg
    (fun φ : SchemeFrobeniusMap X p => φ.inputWeight (e.hom.appTop c))
    (pushforward_openPullback e τ)
  exact hweight.trans hcancel

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: weightedTrace_pullback"

private theorem weightedTrace_pullback (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    ((((polynomialTraceOfOperator (K := K) ψ).toSpec (expChar_pos K p)).pushforward
        (chart A j).isoOpensRange.hom).inputWeight
      ((chartOpen A j).topIso.inv (sectionCoefficientValue m j))).openPullback
        (chart A j).isoOpensRange.hom =
      ((polynomialTraceOfOperator (K := K) ψ).weight (sectionPolynomial m j)).toSpec
        (expChar_pos K p) := by
  let U : (line A).Opens := chartOpen A j
  let e : Spec (.of (Polynomial A)) ≅ U.toScheme := (chart A j).isoOpensRange
  let τ : SchemeFrobeniusMap (Spec (.of (Polynomial A))) p :=
    (polynomialTraceOfOperator (K := K) ψ).toSpec (expChar_pos K p)
  let c : Γ(U.toScheme, ⊤) := U.topIso.inv (sectionCoefficientValue m j)
  let P : Polynomial A := sectionPolynomial m j
  have hcoefficient := congrArg τ.inputWeight (sectionCoefficient_pullback m j)
  have htrace := (traceWeight_toSpec (polynomialTraceOfOperator (K := K) ψ)
    (expChar_pos K p) P).symm
  exact (weighted_pushforward_pullback e τ c).trans (hcoefficient.trans htrace)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: auxiliaryOperator_range_pullback"

private theorem auxiliaryOperator_range_pullback (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    ((auxiliaryOperator (K := K) ψ m).restrict (chartOpen A j)).openPullback
        (chart A j).isoOpensRange.hom =
      ((polynomialTraceOfOperator (K := K) ψ).weight (sectionPolynomial m j)).toSpec
        (expChar_pos K p) := by
  let U : (line A).Opens := chartOpen A j
  let e : Spec (.of (Polynomial A)) ≅ U.toScheme := (chart A j).isoOpensRange
  let Φ : SchemeFrobeniusMap (line A) p := auxiliaryOperator (K := K) ψ m
  calc
    (Φ.restrict U).openPullback e.hom = (Φ.openPullback U.ι).openPullback e.hom :=
      congrArg (fun φ : SchemeFrobeniusMap U.toScheme p => φ.openPullback e.hom)
        (SchemeFrobeniusMap.openPullback_restrict Φ U).symm
    _ = Φ.openPullback (chart A j) := by
      have h := SchemeFrobeniusMap.openPullback_comp Φ e.hom U.ι
      simpa only [e, U, chartOpen, Scheme.Hom.isoOpensRange_hom_ι] using h.symm
    _ = _ := auxiliaryOperator_pullback (K := K) ψ m j

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: chart_precompose_global"

private theorem chart_precompose_global (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p)) (j : indices.{u}) :
    (twistModuleMap (C := K) (q := p) (relativeBase (K := K) (A := A)) m).over (chartOpen A j) ≫
        relativeTwistedCartierChart (K := K) ψ j =
      (schemeOperatorHom (relativeBase (K := K) (A := A))
        (auxiliaryOperator (K := K) ψ m)).over (chartOpen A j) :=
  frobeniusUnit_eq_schemeOperator (relativeBase (K := K) (A := A)) (chartOpen A j)
    (chart A j).isoOpensRange (sectionCoefficientValue m j) (relativeTrace (K := K) ψ j)
    (auxiliaryOperator (K := K) ψ m) (chart_precompose_weight (K := K) ψ m j)
    (relativeTrace_operator (K := K) ψ j)
    ((weightedTrace_pullback (K := K) ψ m j).trans
      (auxiliaryOperator_range_pullback (K := K) ψ m j).symm)


end SchubertGeometry.ProjectiveCartier
