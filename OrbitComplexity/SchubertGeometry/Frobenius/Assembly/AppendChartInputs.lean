import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonMatchingCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordCoordinates
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.DependentChartData
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Original append chart inputs

The chart families come from one fixed retained model. A whole dependent input
equality carries their prescribed maps through the common coframe predicate.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.OperatorSheaf
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private stageRings from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarWordCoordinates
open private appendChartTriangle AppendChartData AppendChartData.I AppendChartData.F
    AppendChartData.N
  AppendChartData.e AppendChartData.sel AppendChartData.V₀ AppendChartData.p
  AppendChartData.c AppendChartData.g AppendChartData.a₀ AppendChartData.hend
  AppendChartContext AppendChartContext.D AppendChartContext.eP AppendChartContext.cD
  AppendChartContext.base AppendChartStage AppendChartStage.q AppendChartStage.V
  AppendChartStage.finite AppendChartStage.affine AppendChartStage.index
  AppendChartStage.eV AppendChartStage.hold AppendChartStage.hbase from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts


open private dependent_chart_data_transport from
    OrbitComplexity.SchubertGeometry.Frobenius.Assembly.DependentChartData

namespace SchubertGeometry.RetainedCharacter

section AtlasAliases

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    {S₀ S : Subalgebra ℤ K} {G : ReductiveGroupData K}
    {word : List G.rootBase.support} {i : G.rootBase.support}
    (hS₀ : S₀ ≤ S) (input : AppendChartData S₀ G word i)
    (old : AppendChartContext input)
    {X : Scheme.{u}} {base : X ⟶ Spec (.of S)}
    {m : bsdhScheme G (word ++ [i]) ⟶ X}
    (d : AppendChartStage S hS₀ old base m)

private abbrev chartCover := AppendChartStage.V d
private abbrev chartNode (z : (chartCover hS₀ input old d).I₀) :=
  (AppendChartStage.index d z).1
private abbrev chartIndex (z : (chartCover hS₀ input old d).I₀) :=
  (AppendChartStage.index d z).2
private abbrev chartChoice (z : (chartCover hS₀ input old d).I₀) :=
  (AppendChartData.sel input) (chartNode hS₀ input old d z)
private abbrev chartSource (z : (chartCover hS₀ input old d).I₀) :=
  (AppendChartData.V₀ input) (chartChoice hS₀ input old d z).1
private abbrev chartPoint (z : (chartCover hS₀ input old d).I₀) :=
  (AppendChartData.g input) (chartChoice hS₀ input old d z).1
private abbrev chartEndpoint (z : (chartCover hS₀ input old d).I₀) :=
  (AppendChartData.a₀ input) (chartChoice hS₀ input old d z).1
private abbrev chartAppend (z : (chartCover hS₀ input old d).I₀) :=
  (AppendChartData.c input) (chartChoice hS₀ input old d z).1
private abbrev chartTriangle (z : (chartCover hS₀ input old d).I₀) :=
  (AppendChartData.hend input) (chartChoice hS₀ input old d z).1
private abbrev chartProjection (z : (chartCover hS₀ input old d).I₀) :=
  (AppendChartData.p input) (chartNode hS₀ input old d z)
    (chartChoice hS₀ input old d z).1 (chartChoice hS₀ input old d z).2
private abbrev chartRing (z : (chartCover hS₀ input old d).I₀) :=
  (@stageRings.{u} K kField kClosed kZero S₀ S G word i hS₀ input).obj
    (chartNode hS₀ input old d z)
private abbrev chartField (z : (chartCover hS₀ input old d).I₀) :=
  (AppendChartData.F input).obj (chartNode hS₀ input old d z)

private instance chart_finite : Finite (chartCover hS₀ input old d).I₀ :=
  AppendChartStage.finite d
private instance chart_affine : ∀ z, IsAffine ((chartCover hS₀ input old d).X z) :=
  AppendChartStage.affine d


end AtlasAliases

end SchubertGeometry.RetainedCharacter
