import Batteries.Tactic.Lint
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import OrbitComplexity.GroupActions.Actions.PullbackFamily
import OrbitComplexity.SchubertGeometry.Cells.CellChart
import OrbitComplexity.SchubertGeometry.Cells.Actions
import OrbitComplexity.SchubertGeometry.Cells.RichardsonActions
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Coordinates and torus families on the specified cell intersection

The coordinate map is defined from the specified closed-pullback projection and
the Gamma-Spec counit. Its square is proved over arbitrary affine schemes
before substitution. The torus family has both original projections.

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u

section Coordinates

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- Coordinates of a specified affine chart map, before any concrete ring is used. -/
def closedChartCoordinates (f : X ⟶ Spec (.of A)) :
    CommRingCat.of A ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop

/-- The counit-coordinate map recovers the original morphism of affine schemes. -/
theorem closedChartCoordinates_square [IsAffine X] (f : X ⟶ Spec (.of A)) :
    Spec.map (closedChartCoordinates f) = X.isoSpec.inv ≫ f := by
  rw [closedChartCoordinates, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
    Scheme.isoSpec_inv_naturality]

/-- A closed chart map has a surjective coordinate map. -/
theorem closedChartCoordinates_surjective (f : X ⟶ Spec (.of A))
    [IsClosedImmersion f] : Function.Surjective (closedChartCoordinates f).hom := by
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  intro b
  obtain ⟨c, hc⟩ := hs b
  obtain ⟨a, ha⟩ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2 c
  refine ⟨a, ?_⟩
  change f.appTop ((Scheme.ΓSpecIso (.of A)).inv a) = b
  rw [ha, hc]

end Coordinates

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- The original scheme-theoretic cell/Richardson pullback. -/
abbrev cellIntersection (a b w : G.weylGroup) : Over (Spec (.of K)) :=
  pullback (schubertCellInclusion G w) (richardsonInclusion G a b)

/-- The inversion-root coordinate algebra of the original cell. -/
abbrev cellAlgebra (w : G.weylGroup) :=
  MvPolynomial {r : G.rootIndex // G.rootBase.IsPos r ∧
    r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w} K

/-- The original inversion-root chart followed by the cell isomorphism. -/
def cellChartOver (w : G.weylGroup) :
    (Spec (.of (cellAlgebra G w))).asOver (Spec (.of K)) ≅
      (schubertCell G w).toOver :=
  (schubertUnipotentChart G w) ≪≫ (schubertCellIso G w)

/-- Forgetting the base in the original cell chart gives its affine scheme chart. -/
def cellCoordinateIso (w : G.weylGroup) :
    Spec (.of (cellAlgebra G w)) ≅ (schubertCell G w).scheme :=
  (Over.forget (Spec (.of K))).mapIso (cellChartOver G w)

/-- Forgetting the base retains the original cell-intersection pullback square. -/
theorem cellIntersection_pullback (a b w : G.weylGroup) :
    IsPullback
      (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left
      (pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b)).left
      (schubertCellInclusion G w).left (richardsonInclusion G a b).left :=
  Functor.map_isPullback (Over.forget (Spec (.of K)))
    (IsPullback.of_hasPullback (schubertCellInclusion G w) (richardsonInclusion G a b))

/-- The specified projection to the Schubert cell is a closed immersion. -/
instance cellIntersection_closed (a b w : G.weylGroup) :
    IsClosedImmersion
      (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left :=
  MorphismProperty.of_isPullback (cellIntersection_pullback G a b w).flip
    (inferInstance : IsClosedImmersion (richardsonInclusion G a b).left)

/-- The specified projection expressed in the fixed inversion-root chart. -/
def cellChartProjection (a b w : G.weylGroup) :
    (cellIntersection G a b w).left ⟶ Spec (.of (cellAlgebra G w)) :=
  (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left ≫
    (cellCoordinateIso G w).inv

/-- Expressing the closed projection in a chart preserves closed immersion. -/
instance cellChartProjection_closed (a b w : G.weylGroup) :
    IsClosedImmersion (cellChartProjection G a b w) := by
  dsimp only [cellChartProjection]
  infer_instance

/-- The specified cell intersection is affine, without reducing it. -/
instance cellIntersection_affine (a b w : G.weylGroup) :
    IsAffine (cellIntersection G a b w).left :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine (cellChartProjection G a b w)).1

/-- The specified coefficient map used to descend the polynomial family. -/
def cellIntersectionCoordinates (a b w : G.weylGroup) :
    CommRingCat.of (cellAlgebra G w) ⟶ Γ((cellIntersection G a b w).left, ⊤) :=
  closedChartCoordinates (cellChartProjection G a b w)

/-- The retained coordinate map is surjective. -/
theorem cellIntersectionCoordinates_surj (a b w : G.weylGroup) :
    Function.Surjective (cellIntersectionCoordinates G a b w).hom :=
  closedChartCoordinates_surjective (cellChartProjection G a b w)

/-- The original coordinate map retains the original closed-pullback projection. -/
theorem cellIntersectionCoordinates_square (a b w : G.weylGroup) :
    Spec.map (cellIntersectionCoordinates G a b w) ≫ (cellCoordinateIso G w).hom =
      (cellIntersection G a b w).left.isoSpec.inv ≫
        (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left := by
  rw [cellIntersectionCoordinates, closedChartCoordinates_square, cellChartProjection]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The given torus family acts on the original scheme-theoretic intersection. -/
def cellTorusFamily (a b w : G.weylGroup) :
    (GroupActions.torusVariety G).toOver ⊗ cellIntersection G a b w ⟶
      cellIntersection G a b w :=
  GroupActions.smulPullbackLift
    (schubertCellInclusion G w) (richardsonInclusion G a b)
    (fst (GroupActions.torusVariety G).toOver (cellIntersection G a b w))
    (snd (GroupActions.torusVariety G).toOver (cellIntersection G a b w) ≫
      pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b))
    (snd (GroupActions.torusVariety G).toOver (cellIntersection G a b w) ≫
      pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b))
    (by simp only [Category.assoc, pullback.condition])

/-- The torus family retains its specified cell projection. -/
theorem cellTorusFamily_fst (a b w : G.weylGroup) :
    cellTorusFamily G a b w ≫
        pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b) =
      (fst (GroupActions.torusVariety G).toOver (cellIntersection G a b w)) •
        (snd (GroupActions.torusVariety G).toOver (cellIntersection G a b w) ≫
        pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)) :=
  GroupActions.smulPullbackLift_fst _ _ _ _ _ _

/-- The torus family retains its specified Richardson projection. -/
theorem cellTorusFamily_snd (a b w : G.weylGroup) :
    cellTorusFamily G a b w ≫
        pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b) =
      (fst (GroupActions.torusVariety G).toOver (cellIntersection G a b w)) •
        (snd (GroupActions.torusVariety G).toOver (cellIntersection G a b w) ≫
        pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b)) :=
  GroupActions.smulPullbackLift_snd _ _ _ _ _ _

end SchubertGeometry.CellContraction
