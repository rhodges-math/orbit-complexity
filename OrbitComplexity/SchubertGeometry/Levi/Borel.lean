import OrbitComplexity.GroupActions.Varieties.ClosedSubgroup
import OrbitComplexity.GroupActions.Varieties.ReductiveVariety
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviIdeal

/-!
# Levi--Borel intersection varieties

The reduced intersection of the standard Levi and Borel point groups is a
closed affine subgroup. Its coordinate quotient gives the ambient inclusion.
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

private theorem leviBorelReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (G.leviBorelIdeal I).toIdeal) := by
  change IsReduced (G.leviBorelAlgebra I)
  infer_instance
attribute [local instance] leviBorelReduced

/-- The reduced closed Levi--Borel subgroup as an affine group variety. -/
def leviBorelVariety (I : Set G.rootBase.support) : Variety K :=
  closedSubgroupVariety G.coordinateAlgebra (G.leviBorelIdeal I)

/-- The reduced Levi--Borel subgroup is a group object. -/
instance leviBorelVarietyGroup (I : Set G.rootBase.support) :
    GrpObj (leviBorelVariety G I).toOver :=
  closedSubgroupVarietyGroup G.coordinateAlgebra (G.leviBorelIdeal I)

/-- The Levi--Borel variety includes into the ambient reductive group. -/
def leviBorelInclusion (I : Set G.rootBase.support) :
    (leviBorelVariety G I).toOver ⟶ (reductiveVariety G).toOver :=
  closedSubgroupInclusion G.coordinateAlgebra (G.leviBorelIdeal I)

/-- The Levi--Borel inclusion is a closed immersion. -/
instance leviBorelInclusion_isClosed (I : Set G.rootBase.support) :
    IsClosedImmersion (leviBorelInclusion G I).left :=
  closedSubgroupInclusion_isClosed G.coordinateAlgebra (G.leviBorelIdeal I)

/-- The Levi--Borel inclusion preserves the group operation. -/
instance leviBorelInclusion_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (leviBorelInclusion G I) :=
  closedSubgroupInclusion_isMonHom G.coordinateAlgebra (G.leviBorelIdeal I)

/-- Levi--Borel rational points identify with their intersection point subgroup. -/
def leviBorelPointsMulEquiv (I : Set G.rootBase.support) :
    (leviBorelVariety G I).points ≃* G.leviBorelPoints I :=
  (closedSubgroupPointsMulEquiv G.coordinateAlgebra (G.leviBorelIdeal I)).trans
    (MulEquiv.subgroupCongr (G.leviBorelIdeal_points I))

/-- The Levi--Borel point identification agrees with the ambient group inclusion. -/
theorem leviBorelInclusion_points (I : Set G.rootBase.support) (l : (leviBorelVariety G I).points) :
    Variety.mapPoints (leviBorelInclusion G I) l =
      reductivePointsMulEquiv G (leviBorelPointsMulEquiv G I l) := by
  have hc : (leviBorelPointsMulEquiv G I l : G.points) =
      (closedSubgroupPointsMulEquiv G.coordinateAlgebra (G.leviBorelIdeal I) l : G.points) :=
    MulEquiv.subgroupCongr_apply (G.leviBorelIdeal_points I) _
  exact (closedSubgroupInclusion_points G.coordinateAlgebra (G.leviBorelIdeal I) l).trans
    (congrArg (affineGroupPointsMulEquiv K G.coordinateAlgebra) hc.symm)


end SchubertGeometry
