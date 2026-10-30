import OrbitComplexity.SchubertGeometry.Levi.Borel
import OrbitComplexity.GroupActions.Varieties.ClosedSubgroupMaps
import OrbitComplexity.GroupActions.Varieties.RootSubgroupPoints
import OrbitComplexity.GroupActions.Varieties.TorusPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviInclusions

/-! # Closed inclusions in the Levi--Borel group

The torus and the positive Levi root subgroup include by quotient Hopf maps.
Both inclusions preserve their ambient reductive group points.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem coordinateReduced : IsReduced G.coordinateAlgebra := by
  let : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
  exact TauCeti.isReduced_of_smooth K G.coordinateAlgebra
attribute [local instance] coordinateReduced

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced (G.coordinateAlgebra ⧸ G.torusIdeal.toIdeal) := by
  change IsReduced G.torusAlgebra
  let : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra
attribute [local instance] torusReduced

private theorem leviBorelReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (G.leviBorelIdeal I).toIdeal) := by
  change IsReduced (G.leviBorelAlgebra I)
  infer_instance
attribute [local instance] leviBorelReduced

private theorem rootReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (G.rootSubsetIdeal (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I)).toIdeal) := by
  change IsReduced (G.rootSubsetAlgebra _ _)
  infer_instance
attribute [local instance] rootReduced

private theorem leviBorelIdeal_le_root (I : Set G.rootBase.support) :
    G.leviBorelIdeal I ≤ G.rootSubsetIdeal (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I) := by
  apply TauCeti.HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  exact (G.rootSubsetPoints_le_leviBorel I _ _ (fun _ h => h)).trans_eq
    (G.leviBorelIdeal_points I).symm

/-- The chosen torus includes as a closed subgroup of the Levi--Borel group. -/
def torusLeviBorelInclusion (I : Set G.rootBase.support) :
    (torusVariety G).toOver ⟶ (leviBorelVariety G I).toOver :=
  closedSubgroupMap G.coordinateAlgebra (G.leviBorelIdeal I) G.torusIdeal
    (G.leviBorelIdeal_le_torus I)

/-- The torus inclusion into the Levi--Borel group is a closed immersion. -/
instance torusLeviBorelInclusion_isClosed (I : Set G.rootBase.support) :
    IsClosedImmersion (torusLeviBorelInclusion G I).left :=
  closedSubgroupMap_isClosed _ _ _ _

/-- The torus inclusion into the Levi--Borel group preserves multiplication. -/
instance torusLeviBorelInclusion_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (torusLeviBorelInclusion G I) := closedSubgroupMap_isMonHom _ _ _ _

/-- The nested torus inclusion agrees with its inclusion in the reductive group. -/
theorem torusLeviBorelInclusion_comp (I : Set G.rootBase.support) :
    torusLeviBorelInclusion G I ≫ leviBorelInclusion G I = torusInclusion G :=
  closedSubgroupMap_comp_inclusion _ _ _ _

/-- The torus inclusion in the Levi--Borel group preserves its ambient point. -/
theorem torusLeviBorelInclusion_points (I : Set G.rootBase.support)
    (t : (torusVariety G).points) :
    (leviBorelPointsMulEquiv G I (Variety.mapPoints (torusLeviBorelInclusion G I) t) : G.points) =
      (torusPointsMulEquiv G t : G.points) := by
  apply (reductivePointsMulEquiv G).injective
  have he : Variety.mapPoints (leviBorelInclusion G I)
      (Variety.mapPoints (torusLeviBorelInclusion G I) t) =
        Variety.mapPoints (torusInclusion G) t := by
    rw [← Variety.mapPoints_comp, torusLeviBorelInclusion_comp]
  exact (leviBorelInclusion_points G I _).symm.trans (he.trans (torusInclusion_points G t))

/-- The positive Levi root subgroup includes into the Levi--Borel group. -/
def leviRootBorelInclusion (I : Set G.rootBase.support) :
    (rootSubsetVariety G (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I)).toOver ⟶
      (leviBorelVariety G I).toOver :=
  closedSubgroupMap G.coordinateAlgebra (G.leviBorelIdeal I) _ (leviBorelIdeal_le_root G I)

/-- The positive Levi root inclusion is a closed immersion. -/
instance leviRootBorelInclusion_isClosed (I : Set G.rootBase.support) :
    IsClosedImmersion (leviRootBorelInclusion G I).left := closedSubgroupMap_isClosed _ _ _ _

/-- The positive Levi root inclusion preserves multiplication. -/
instance leviRootBorelInclusion_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (leviRootBorelInclusion G I) := closedSubgroupMap_isMonHom _ _ _ _

/-- The nested positive Levi root inclusion agrees with its ambient inclusion. -/
theorem leviRootBorelInclusion_comp (I : Set G.rootBase.support) :
    leviRootBorelInclusion G I ≫ leviBorelInclusion G I =
      rootSubsetInclusion G (leviPositiveRoots G.rootBase I)
        (LeviRootSpan.isPositiveRootClosed G.rootBase I) :=
  closedSubgroupMap_comp_inclusion _ _ _ _

/-- The positive Levi root inclusion preserves its ambient group point. -/
theorem leviRootBorelInclusion_points (I : Set G.rootBase.support)
    (u : (rootSubsetVariety G (leviPositiveRoots G.rootBase I)
      (LeviRootSpan.isPositiveRootClosed G.rootBase I)).points) :
    (leviBorelPointsMulEquiv G I (Variety.mapPoints (leviRootBorelInclusion G I) u) : G.points) =
      (rootSubsetPointsMulEquiv G _ (LeviRootSpan.isPositiveRootClosed G.rootBase I) u :
        G.points) := by
  apply (reductivePointsMulEquiv G).injective
  have he : Variety.mapPoints (leviBorelInclusion G I)
      (Variety.mapPoints (leviRootBorelInclusion G I) u) =
        Variety.mapPoints (rootSubsetInclusion G _ _) u := by
    rw [← Variety.mapPoints_comp, leviRootBorelInclusion_comp]
  exact (leviBorelInclusion_points G I _).symm.trans
    (he.trans (rootSubsetInclusion_points G _ _ u))

end SchubertGeometry
