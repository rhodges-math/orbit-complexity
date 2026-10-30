import OrbitComplexity.SchubertGeometry.FlagBundle.Projection
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth associated bundles

The projection of an associated bundle with smooth fibre is smooth, since its local
product projections are base changes of the fibre's structure morphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)
  (Y : GroupActions.Variety K) [ModObj (GroupActions.borelVariety G).toOver Y.toOver]

/-- An associated bundle with smooth fibre has smooth projection. -/
instance flagBundleProjection_smooth [Smooth Y.toSpec] :
    Smooth (flagBundleProjection G Y) := by
  let : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Smooth.{u})
  apply IsZariskiLocalAtTarget.of_openCover (P := @Smooth.{u}) (flagSchemeCover G)
  intro g
  change G.points at g
  change Smooth (pullback.snd (flagBundleProjection G Y) (flagChartMorphism G g).left)
  have : Smooth (fst (GroupActions.oppositeUnipotentVariety G).toOver Y.toOver).left := by
    change Smooth (pullback.fst (GroupActions.oppositeUnipotentVariety G).toSpec Y.toSpec)
    infer_instance
  rw [← (flagBundlePullback G Y g).flip.isoPullback_inv_snd]
  infer_instance

end SchubertGeometry
