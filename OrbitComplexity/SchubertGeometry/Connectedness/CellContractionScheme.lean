import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CellConnected
import OrbitComplexity.SchubertGeometry.Connectedness.RootChartOrigin
import OrbitComplexity.FrobeniusSplitting.Normality.PolynomialScheme

/-!
# The original polynomial contraction and its exact Weyl anchor

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u

attribute [local instance] coefficientAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- The original quotient contraction as a scheme morphism into the same intersection. -/
def cellPolynomialContraction (a b w : G.weylGroup) :
    Spec (.of (Polynomial (cellCoefficients G a b w))) ⟶
      (cellIntersection G a b w).left :=
  Spec.map (CommRingCat.ofHom (cellContractionAlg G a b w).toRingHom) ≫
    (cellIntersection G a b w).left.isoSpec.inv

/-- The specified scalar origin of the original nonempty intersection. -/
def cellOrigin (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left) :
    Spec (.of K) ⟶ (cellIntersection G a b w).left :=
  Spec.map (CommRingCat.ofHom (cellOriginAlg G a b w hne).toRingHom) ≫
    (cellIntersection G a b w).left.isoSpec.inv

/-- The derived origin has exactly the original root-coordinate origin in the cell. -/
theorem cellOrigin_chart (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left) :
    cellOrigin G a b w hne ≫
        (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (fun _ => (0 : K)) : cellAlgebra G w →ₐ[K] K).toRingHom) ≫
          (cellCoordinateIso G w).hom := by
  have hq : Spec.map (CommRingCat.ofHom
      (cellIntersectionAlgMap G a b w).toRingHom) ≫ (cellCoordinateIso G w).hom =
        (cellIntersection G a b w).left.isoSpec.inv ≫
          (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left := by
    rw [cellIntersectionAlgMap_eq]
    exact cellIntersectionCoordinates_square G a b w
  exact (Category.assoc
    (Spec.map (CommRingCat.ofHom (cellOriginAlg G a b w hne).toRingHom))
    (cellIntersection G a b w).left.isoSpec.inv
    (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left).trans
    (FrobeniusSplitting.originChart_image (cellIntersectionAlgMap G a b w)
      (cellOriginAlg G a b w hne) (MvPolynomial.aeval (fun _ => (0 : K)))
      (cellOriginAlg_comp G a b w hne) (cellCoordinateIso G w)
      (cellIntersection G a b w).left.isoSpec.symm
      (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left hq)

/-- The specified cell projection of the derived origin is the specified Weyl flag. -/
theorem cellOrigin_flag (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left) :
    cellOrigin G a b w hne ≫
        (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left ≫
          (schubertCellInclusion G w).left =
      ((flagVariety G).pointsEquivOverHom (weylFlagPoint G w)).left := by
  rw [← Category.assoc, cellOrigin_chart]
  simpa only [Category.assoc] using cellChart_origin G w

/-- The derived Weyl anchor lies in the original Richardson target. -/
def cellRichardsonAnchor (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left) :
    Spec (.of K) ⟶ (richardsonVariety G a b).scheme :=
  cellOrigin G a b w hne ≫
    (pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b)).left

/-- The original Richardson inclusion sends the derived anchor to the same Weyl flag. -/
theorem cellRichardsonAnchor_flag (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left) :
    cellRichardsonAnchor G a b w hne ≫ (richardsonInclusion G a b).left =
      ((flagVariety G).pointsEquivOverHom (weylFlagPoint G w)).left := by
  have hs := congrArg Over.Hom.left
    (pullback.condition (f := schubertCellInclusion G w) (g := richardsonInclusion G a b))
  simp only [Over.comp_left] at hs
  rw [cellRichardsonAnchor, Category.assoc, ← hs]
  exact cellOrigin_flag G a b w hne

end SchubertGeometry.CellContraction
