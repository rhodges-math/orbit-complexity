import Batteries.Tactic.Lint
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import OrbitComplexity.SchubertGeometry.Connectedness.AffineChartAlgebra

/-!
# Relative coefficients of the original closed cell intersection

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u

attribute [local instance] coefficientAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- The specified global coordinate ring of the original cell intersection. -/
abbrev cellCoefficients (a b w : G.weylGroup) :=
  Γ((cellIntersection G a b w).left, ⊤)

/-- The original closed projection expressed in the original relative cell chart. -/
def cellChartMapOver (a b w : G.weylGroup) :
    cellIntersection G a b w ⟶
      (Spec (.of (cellAlgebra G w))).asOver (Spec (.of K)) :=
  pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b) ≫
    (cellChartOver G w).inv

/-- The base-algebra coordinate map of that same closed projection. -/
def cellIntersectionAlgMap (a b w : G.weylGroup) :
    cellAlgebra G w →ₐ[K] cellCoefficients G a b w :=
  chartAlgHom (cellIntersection G a b w) (cellChartMapOver G a b w)

/-- Its underlying ring map is exactly the already specified counit coordinate map. -/
theorem cellIntersectionAlgMap_eq (a b w : G.weylGroup) :
    CommRingCat.ofHom (cellIntersectionAlgMap G a b w).toRingHom =
      cellIntersectionCoordinates G a b w :=
  chartAlgHom_eq (cellIntersection G a b w) (cellChartMapOver G a b w)

/-- The specified algebra coordinate map is surjective. -/
theorem cellIntersectionAlgMap_surj (a b w : G.weylGroup) :
    Function.Surjective (cellIntersectionAlgMap G a b w) := by
  have he := congrArg (fun f : CommRingCat.of (cellAlgebra G w) ⟶
    CommRingCat.of (cellCoefficients G a b w) => f.hom)
      (cellIntersectionAlgMap_eq G a b w)
  change Function.Surjective
    (CommRingCat.ofHom (cellIntersectionAlgMap G a b w).toRingHom).hom
  rw [he]
  exact cellIntersectionCoordinates_surj G a b w

/-- The relative affine counit and original projection have the specified chart square. -/
theorem cellIntersectionAlgMap_square (a b w : G.weylGroup) :
    Spec.map (CommRingCat.ofHom (cellIntersectionAlgMap G a b w).toRingHom) ≫
        (cellCoordinateIso G w).hom =
      (coefficientIso (cellIntersection G a b w)).hom.left ≫
        (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left := by
  rw [cellIntersectionAlgMap_eq, cellIntersectionCoordinates_square,
    coefficientIso_hom_left]
  rfl

/-- The original coordinate map, cell chart and intersection projection commute over K. -/
theorem cellIntersectionAlgMap_over (a b w : G.weylGroup) :
    GroupActions.algebraSpecMap (cellIntersectionAlgMap G a b w) ≫
        (cellChartOver G w).hom =
      (coefficientIso (cellIntersection G a b w)).hom ≫
        pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b) := by
  rw [cellIntersectionAlgMap, chartAlgHom_over_square, cellChartMapOver]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SchubertGeometry.CellContraction
