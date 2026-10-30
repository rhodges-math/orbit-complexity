import OrbitComplexity.SchubertGeometry.FlagBundle.Transitions
import OrbitComplexity.GroupActions.Varieties.ProductImmersions

/-! # Gluing bundles over the flag variety

The product charts of a variety with a Borel action glue through their transition factors.
The overlap isomorphisms and their cocycle define the associated bundle scheme.
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

private def bundleTripleMap (g h k : G.points) :
    pullback (flagBundleInclusion G Y g h).left (flagBundleInclusion G Y g k).left ⟶
      pullback (flagBundleInclusion G Y h k).left (flagBundleInclusion G Y h g).left :=
  (flagBundleTripleIso G Y g h k).inv ≫ (flagBundleTripleTransition G Y g h k).left ≫
    (flagBundleTripleIso G Y h k g).hom

private theorem bundleTripleMap_snd (g h k : G.points) :
    bundleTripleMap G Y g h k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ (flagBundleTransition G Y g h).left := by
  apply (cancel_epi (flagBundleTripleIso G Y g h k).hom).mp
  dsimp only [bundleTripleMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, flagBundleTripleIso_snd]
  have he := congrArg Over.Hom.left (flagBundleTripleTransition_snd G Y g h k)
  rw [← Category.assoc, flagBundleTripleIso_fst]
  exact he

private theorem bundleTripleMap_cycle (g h k : G.points) :
    bundleTripleMap G Y g h k ≫ bundleTripleMap G Y h k g ≫
      bundleTripleMap G Y k g h = 𝟙 _ := by
  have he := congrArg (fun f => (flagBundleTripleIso G Y g h k).inv ≫
    f.left ≫ (flagBundleTripleIso G Y g h k).hom)
    (flagBundleTripleTransition_cycle G Y g h k)
  simpa only [bundleTripleMap, Over.comp_left, Over.id_left, Category.assoc,
    Iso.hom_inv_id_assoc, Category.id_comp, Iso.inv_hom_id] using he

/-- The scheme gluing data of a bundle constructed from a Borel action. -/
def flagBundleGlueData : Scheme.GlueData where
  J := G.points
  U _ := ((GroupActions.oppositeUnipotentVariety G).toOver ⊗ Y.toOver).left
  V ij := ((flagOverlapVariety G ij.1 ij.2).toOver ⊗ Y.toOver).left
  f g h := (flagBundleInclusion G Y g h).left
  f_open g h := by infer_instance
  f_id g := by
    have : IsIso ((Over.forget (Spec (CommRingCat.of K))).map (flagOverlapInclusion G g g)) := by
      change IsIso (flagOverlapInclusion G g g).left
      infer_instance
    have : IsIso (flagOverlapInclusion G g g) :=
      isIso_of_reflects_iso _ (Over.forget (Spec (CommRingCat.of K)))
    change IsIso ((Over.forget (Spec (CommRingCat.of K))).map (flagBundleInclusion G Y g g))
    infer_instance
  t g h := (flagBundleTransition G Y g h).left
  t_id g := congrArg Over.Hom.left (flagBundleTransition_self G Y g)
  t' g h k := bundleTripleMap G Y g h k
  t_fac g h k := bundleTripleMap_snd G Y g h k
  cocycle g h k := bundleTripleMap_cycle G Y g h k

end SchubertGeometry
