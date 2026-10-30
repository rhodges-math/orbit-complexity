import OrbitComplexity.SchubertGeometry.Parabolics.LeviDecompositionPoints
import OrbitComplexity.SchubertGeometry.Levi.Reductive
import OrbitComplexity.GroupActions.Varieties.ClosedSubgroupMaps
import OrbitComplexity.GroupActions.Varieties.RootSubgroupPoints

/-! # Closed factors of standard parabolics

The Levi and the outside-subsystem positive-root group include into the parabolic
through the corresponding quotient Hopf algebras.
-/

noncomputable section
namespace SchubertGeometry
open ReductiveGroups GroupActions CategoryTheory AlgebraicGeometry TauCeti
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

omit [IsAlgClosed K] [CharZero K] in
private theorem coordinateReduced : IsReduced G.coordinateAlgebra := by
  let : Algebra.Smooth K G.coordinateAlgebra := G.reductive.smooth
  exact TauCeti.isReduced_of_smooth K G.coordinateAlgebra
attribute [local instance] coordinateReduced

private abbrev parabolicIdeal (I : Set G.rootBase.support) : HopfIdeal K G.coordinateAlgebra :=
  HopfIdeal.vanishingIdeal (standardParabolicPoints G I)

/-- The coordinate Hopf algebra of the reduced standard parabolic subgroup. -/
abbrev parabolicAlgebra (I : Set G.rootBase.support) : FiniteTypeCommHopfAlgCat.{u, u} K :=
  FiniteTypeCommHopfAlgCat.quotient G.coordinateAlgebra (parabolicIdeal G I)

private theorem parabolicReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (parabolicIdeal G I).toIdeal) := by
  change IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K G.coordinateAlgebra)
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)))
  infer_instance

private theorem leviReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (G.leviIdeal I).toIdeal) := by
  change IsReduced (G.leviAlgebra I)
  infer_instance

private theorem rootReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (G.rootSubsetIdeal (parabolicRadicalRoots G.rootBase I)
      (parabolicRadicalRoots_closed G.rootBase I)).toIdeal) := by
  change IsReduced (G.rootSubsetAlgebra _ _)
  infer_instance
attribute [local instance] parabolicReduced leviReduced rootReduced

private theorem levi_le_parabolic (I : Set G.rootBase.support) :
    G.leviPoints I ≤ standardParabolicPoints G I := by
  rw [parabolic_eq_levi_sup_unipotent]
  exact le_sup_left

private theorem root_le_parabolic (I : Set G.rootBase.support) :
    parabolicUnipotentPoints G I ≤ standardParabolicPoints G I := by
  rw [parabolic_eq_levi_sup_unipotent]
  exact le_sup_right

private theorem parabolicIdeal_le_levi (I : Set G.rootBase.support) :
    parabolicIdeal G I ≤ G.leviIdeal I := by
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  exact (G.leviIdeal_points I).le.trans ((levi_le_parabolic G I).trans
    ((HopfIdeal.le_vanishingIdeal_iff _ (parabolicIdeal G I)).mp le_rfl))

private theorem parabolicIdeal_le_root (I : Set G.rootBase.support) :
    parabolicIdeal G I ≤ G.rootSubsetIdeal (parabolicRadicalRoots G.rootBase I)
      (parabolicRadicalRoots_closed G.rootBase I) := by
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  exact (root_le_parabolic G I).trans
    ((HopfIdeal.le_vanishingIdeal_iff _ (parabolicIdeal G I)).mp le_rfl)

/-- The unipotent factor supported on positive roots outside the Levi subsystem. -/
abbrev parabolicUnipotentVariety (I : Set G.rootBase.support) : Variety K :=
  rootSubsetVariety G (parabolicRadicalRoots G.rootBase I)
    (parabolicRadicalRoots_closed G.rootBase I)

/-- The standard Levi includes as a closed subgroup of the standard parabolic. -/
def leviParabolicInclusion (I : Set G.rootBase.support) :
    (leviVariety G I).toOver ⟶ (standardParabolicVariety G I).toOver :=
  closedSubgroupMap G.coordinateAlgebra (parabolicIdeal G I) (G.leviIdeal I)
    (parabolicIdeal_le_levi G I)

/-- The Levi inclusion into the parabolic is a closed immersion. -/
instance leviParabolicInclusion_isClosed (I : Set G.rootBase.support) :
    IsClosedImmersion (leviParabolicInclusion G I).left :=
  closedSubgroupMap_isClosed _ _ _ _

/-- The Levi inclusion into the parabolic preserves multiplication. -/
instance leviParabolicInclusion_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (leviParabolicInclusion G I) := closedSubgroupMap_isMonHom _ _ _ _

/-- The Levi inclusion in the parabolic agrees with its ambient group inclusion. -/
@[reassoc]
theorem leviParabolicInclusion_comp (I : Set G.rootBase.support) :
    leviParabolicInclusion G I ≫ standardParabolicInclusion G I = leviInclusion G I :=
  closedSubgroupMap_comp_inclusion _ _ _ _

/-- Inclusion of a Levi point in the parabolic preserves its ambient group value. -/
theorem leviParabolicInclusion_points (I : Set G.rootBase.support)
    (l : (leviVariety G I).points) :
    (parabolicPointsMulEquiv G I (Variety.mapPoints (leviParabolicInclusion G I) l) :
      G.points) = (leviPointsMulEquiv G I l : G.points) := by
  have he : Variety.mapPoints (standardParabolicInclusion G I)
      (Variety.mapPoints (leviParabolicInclusion G I) l) =
      Variety.mapPoints (leviInclusion G I) l := by
    rw [← Variety.mapPoints_comp, leviParabolicInclusion_comp]
  rw [parabolicInclusion_points, leviInclusion_points] at he
  exact (reductivePointsMulEquiv G).injective he

/-- The outside-subsystem positive-root group includes in the standard parabolic. -/
def parabolicUnipotentInclusion (I : Set G.rootBase.support) :
    (parabolicUnipotentVariety G I).toOver ⟶ (standardParabolicVariety G I).toOver :=
  closedSubgroupMap G.coordinateAlgebra (parabolicIdeal G I) _ (parabolicIdeal_le_root G I)

/-- The unipotent-factor inclusion into the parabolic is a closed immersion. -/
instance parabolicUnipotentInclusion_isClosed (I : Set G.rootBase.support) :
    IsClosedImmersion (parabolicUnipotentInclusion G I).left :=
  closedSubgroupMap_isClosed _ _ _ _

/-- The unipotent-factor inclusion into the parabolic preserves multiplication. -/
instance parabolicUnipotentInclusion_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (parabolicUnipotentInclusion G I) := closedSubgroupMap_isMonHom _ _ _ _

/-- The unipotent-factor inclusion agrees with the root subgroup's ambient inclusion. -/
@[reassoc]
theorem parabolicUnipotentInclusion_comp (I : Set G.rootBase.support) :
    parabolicUnipotentInclusion G I ≫ standardParabolicInclusion G I =
      rootSubsetInclusion G _ (parabolicRadicalRoots_closed G.rootBase I) :=
  closedSubgroupMap_comp_inclusion _ _ _ _

/-- Inclusion of a unipotent-factor point preserves its ambient group value. -/
theorem parabolicUnipotentInclusion_points (I : Set G.rootBase.support)
    (r : (parabolicUnipotentVariety G I).points) :
    (parabolicPointsMulEquiv G I (Variety.mapPoints (parabolicUnipotentInclusion G I) r) :
      G.points) = (rootSubsetPointsMulEquiv G _
        (parabolicRadicalRoots_closed G.rootBase I) r : G.points) := by
  have he : Variety.mapPoints (standardParabolicInclusion G I)
      (Variety.mapPoints (parabolicUnipotentInclusion G I) r) =
      Variety.mapPoints (rootSubsetInclusion G _ (parabolicRadicalRoots_closed G.rootBase I)) r :=
        by rw [← Variety.mapPoints_comp, parabolicUnipotentInclusion_comp]
  rw [parabolicInclusion_points, rootSubsetInclusion_points] at he
  exact (reductivePointsMulEquiv G).injective he

end SchubertGeometry
