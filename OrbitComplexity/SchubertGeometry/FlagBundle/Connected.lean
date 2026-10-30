import OrbitComplexity.SchubertGeometry.FlagBundle.Projection
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Geometric fibres of associated flag bundles

The flag atlas identifies each restricted projection with a product projection.
Geometric connectedness and geometric integrality therefore descend from the fibre.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u

namespace SchubertGeometry

private instance integralIsoClosed :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsIntegral ·) :=
  ⟨fun e h => by
    have : IsIntegral _ := h
    exact IsIntegral.of_isIso e.hom⟩

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
  (Y : GroupActions.Variety K) [ModObj (GroupActions.borelVariety G).toOver Y.toOver]

private theorem projection_geometrically (Q : ObjectProperty Scheme.{u})
    [Q.IsClosedUnderIsomorphisms] (hY : geometrically Q Y.toSpec) :
    geometrically Q (flagBundleProjection G Y) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := geometrically Q) (flagSchemeCover G)
  intro g
  change G.points at g
  change geometrically Q
    (pullback.snd (flagBundleProjection G Y) (flagChartMorphism G g).left)
  have hq : geometrically Q
      (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver).left := by
    change geometrically Q
      (pullback.fst (GroupActions.oppositeUnipotentVariety G).toSpec Y.toSpec)
    exact MorphismProperty.pullback_fst _ _ hY
  rw [← (flagBundlePullback G Y g).flip.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso (geometrically Q) _ _).mpr hq

/-- A geometrically connected fibre gives a geometrically connected bundle projection. -/
instance flagBundle_geometricallyConnected [GeometricallyConnected Y.toSpec] :
    GeometricallyConnected (flagBundleProjection G Y) := by
  constructor
  exact projection_geometrically G Y (ConnectedSpace ·)
    (GeometricallyConnected.geometrically_connectedSpace (f := Y.toSpec))

/-- A geometrically integral fibre gives a geometrically integral bundle projection. -/
instance flagBundle_geometricallyIntegral [GeometricallyIntegral Y.toSpec] :
    GeometricallyIntegral (flagBundleProjection G Y) := by
  constructor
  exact projection_geometrically G Y (IsIntegral ·)
    (GeometricallyIntegral.geometrically_isIntegral (f := Y.toSpec))

end SchubertGeometry
