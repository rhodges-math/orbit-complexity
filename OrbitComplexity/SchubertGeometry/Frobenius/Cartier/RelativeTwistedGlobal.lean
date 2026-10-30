import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Gluing relative Cartier maps from the degree line source -/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GroupActions FrobeniusSplitting FrobeniusSplitting.OperatorSheaf
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open RelativeGlue

open private indices line chart chartOpen relativeBase sourceLine unitLine
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

open private auxiliaryFrame auxiliaryFrame_over_isIso
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedFrame

open private auxiliaryOperator
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedSections

open private chart_precompose_global
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedComparison

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

private abbrev operatorSource : (line A).Modules :=
  frobeniusRestriction K p (relativeBase (K := K) (A := A))
    (sourceLine (A := A) (p := p))

private abbrev chartOperator (ψ : FrobeniusLinearMap A p) (j : indices.{u}) :
    (operatorSource (K := K) (A := A) (p := p)).over (chartOpen A j) ⟶
      (unitLine (A := A)).over (chartOpen A j) :=
  relativeTwistedCartierChart (K := K) ψ j

private def restrictedChartOperator (ψ : FrobeniusLinearMap A p) (j : indices.{u})
    (W : (line A).Opens) (h : W ≤ chartOpen A j) :
    (operatorSource (K := K) (A := A) (p := p)).over W ⟶ (unitLine (A := A)).over W :=
  restrictModuleHom (operatorSource (K := K) (A := A) (p := p))
    (unitLine (A := A)) h (chartOperator (K := K) ψ j)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: chart_precompose_value"

private theorem chart_precompose_value (ψ : FrobeniusLinearMap A p)
    (m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p))
    (j : indices.{u}) (V : Over (chartOpen A j)) (a : Γ(line A, V.left)) :
    ((chartOperator (K := K) ψ j).val.app (op V)).hom
        ((m.val.app (op V.left)).hom a) =
      ((schemeOperatorHom (relativeBase (K := K) (A := A))
        (auxiliaryOperator (K := K) ψ m)).val.app (op V.left)).hom a := by
  have h := chart_precompose_global (K := K) ψ m j
  exact congrArg (fun q : (frobeniusRestriction K p (relativeBase (K := K) (A := A))
      (unitLine (A := A))).over (chartOpen A j) ⟶ (unitLine (A := A)).over (chartOpen A j) =>
    (q.val.app (op V)).hom a) h

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: chart_maps_agree"

private theorem chart_maps_agree (ψ : FrobeniusLinearMap A p) (W : (line A).Opens)
    (h₀W : W ≤ chartOpen A ⟨0⟩) (h₁W : W ≤ chartOpen A ⟨1⟩) :
    restrictedChartOperator (K := K) ψ ⟨0⟩ W h₀W =
      restrictedChartOperator (K := K) ψ ⟨1⟩ W h₁W := by
  let m : unitLine (A := A) ⟶ sourceLine (A := A) (p := p) :=
    auxiliaryFrame A (p - 1)
  let : IsIso (m.over (chartOpen A ⟨0⟩)) :=
    auxiliaryFrame_over_isIso A (p - 1)
  exact cancel_frame_overlaps K p (relativeBase (K := K) (A := A))
    (sourceLine (A := A) (p := p)) m (chartOpen A ⟨0⟩) (chartOpen A ⟨1⟩) W h₀W h₁W
    (chartOperator (K := K) ψ ⟨0⟩) (chartOperator (K := K) ψ ⟨1⟩)
    (schemeOperatorHom (relativeBase (K := K) (A := A)) (auxiliaryOperator (K := K) ψ m))
    (chart_precompose_value (K := K) ψ m ⟨0⟩)
    (chart_precompose_value (K := K) ψ m ⟨1⟩)

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: originalCharts_cover"

private theorem originalCharts_cover : (⨆ j : indices.{u}, chartOpen A j) = ⊤ := by
  have h := (projectiveChartCover A indices.{u}).iSup_opensRange
  change (⨆ j : indices.{u}, (projectiveChartMap A indices.{u} j).opensRange) = ⊤ at h
  simpa only [chartOpen, chart, projectiveLinePolynomialChart_range,
    projectiveChartMap_range] using h

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: chart_family_compatible"

private theorem chart_family_compatible (ψ : FrobeniusLinearMap A p) :
    TopCat.Presheaf.IsCompatible
      (SheafOfModules.linearHom (operatorSource (K := K) (A := A) (p := p))
        (unitLine (A := A))).obj (chartOpen A) (fun j =>
        (SheafOfModules.linearHomObjEquiv
          (operatorSource (K := K) (A := A) (p := p))
          (unitLine (A := A)) (chartOpen A j)).symm (chartOperator (K := K) ψ j)) := by
  intro i j
  apply (SheafOfModules.linearHomObjEquiv
    (operatorSource (K := K) (A := A) (p := p)) (unitLine (A := A))
    (chartOpen A i ⊓ chartOpen A j)).injective
  change restrictedChartOperator (K := K) ψ i _ inf_le_left =
    restrictedChartOperator (K := K) ψ j _ inf_le_right
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact chart_maps_agree (K := K) ψ _ inf_le_left inf_le_right
  · exact (chart_maps_agree (K := K) ψ _ inf_le_right inf_le_left).symm
  · rfl

run_cmd do
  if Lean.profiler.get (← Lean.MonadOptions.getOptions) then
    IO.eprintln "Cartier: exists_relativeTwistedCartierMap"

private theorem exists_relativeTwistedCartierMap (ψ : FrobeniusLinearMap A p) :
    ∃ Θ : operatorSource (K := K) (A := A) (p := p) ⟶ unitLine (A := A),
      ∀ j : indices.{u}, Θ.over (chartOpen A j) = chartOperator (K := K) ψ j :=
  glueModuleMorphisms (chartOpen A) originalCharts_cover
    (operatorSource (K := K) (A := A) (p := p)) (unitLine (A := A))
    (chartOperator (K := K) ψ) (chart_family_compatible (K := K) ψ)

/-- The two original line-source charts glue for an arbitrary coefficient prior.
The source includes the infinity factor and contains no determinant insertion. -/
def relativeTwistedCartierMap (ψ : FrobeniusLinearMap A p) :
    frobeniusRestriction K p (relativeBase (K := K) (A := A))
      (sourceLine (A := A) (p := p)) ⟶ unitLine (A := A) :=
  Classical.choose (exists_relativeTwistedCartierMap (K := K) ψ)

/-- The glued map retains each original polynomial-chart morphism. -/
theorem relativeTwistedCartierMap_chart (ψ : FrobeniusLinearMap A p) (j : indices.{u}) :
    (relativeTwistedCartierMap (K := K) ψ).over (chartOpen A j) =
      relativeTwistedCartierChart (K := K) ψ j :=
  Classical.choose_spec (exists_relativeTwistedCartierMap (K := K) ψ) j

end SchubertGeometry.ProjectiveCartier
