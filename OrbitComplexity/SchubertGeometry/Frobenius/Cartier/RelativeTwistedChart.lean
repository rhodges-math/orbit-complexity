import OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource
import Batteries.Tactic.OpenPrivate

/-! # The relative Cartier chart formula on each subopen -/

open AlgebraicGeometry CategoryTheory Opposite
open FrobeniusSplitting
noncomputable section
universe u

namespace SchubertGeometry.ProjectiveCartier

open private indices chartOpen sourceLine relativeTrace infinityCoefficient relativeChart_value
  from OrbitComplexity.SchubertGeometry.Frobenius.Cartier.RelativeTwistedChartSource

variable {K : Type u} [Field K] {p : ℕ} [ExpChar K p] [PerfectRing K p]
variable {A : Type u} [CommRing A] [Algebra K A]

/-- On every original subopen, the map traces the specified chart coordinate
after applying the infinity factor; it never inserts the endpoint section. -/
theorem relativeTwistedCartierChart_apply (ψ : FrobeniusLinearMap A p)
    (j : indices.{u}) (V : Over (chartOpen A j))
    (s : (sourceLine (A := A) (p := p)).val.obj (op V.left)) :
    ((relativeTwistedCartierChart (K := K) ψ j).val.app (op V)).hom s =
      ((relativeTrace (K := K) ψ j).val.app (op V)).hom
        (((infinityCoefficient (A := A) (p := p) j).val.app (op V)).hom s) :=
  relativeChart_value (K := K) ψ j V s

end SchubertGeometry.ProjectiveCartier
