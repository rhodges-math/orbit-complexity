import OrbitComplexity.GroupActions.Varieties.ClosedSubgroup
import OrbitComplexity.GroupActions.Varieties.ReductiveVariety
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviIdeal

/-!
# Standard Levi group varieties

The reduced selected-character centralizer is a closed affine subgroup of the
reductive group. Its rational points are the centralizer point group.
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

private theorem leviReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (G.leviIdeal I).toIdeal) := by
  change IsReduced (G.leviAlgebra I)
  infer_instance
attribute [local instance] leviReduced

/-- The reduced closed standard Levi subgroup as an affine group variety. -/
def leviVariety (I : Set G.rootBase.support) : Variety K :=
  closedSubgroupVariety G.coordinateAlgebra (G.leviIdeal I)

/-- The reduced standard Levi subgroup is a group object. -/
instance leviVarietyGroup (I : Set G.rootBase.support) : GrpObj (leviVariety G I).toOver :=
  closedSubgroupVarietyGroup G.coordinateAlgebra (G.leviIdeal I)

/-- The standard Levi variety includes into the ambient reductive group. -/
def leviInclusion (I : Set G.rootBase.support) :
    (leviVariety G I).toOver ⟶ (reductiveVariety G).toOver :=
  closedSubgroupInclusion G.coordinateAlgebra (G.leviIdeal I)

/-- The standard Levi inclusion is a closed immersion. -/
instance leviInclusion_isClosed (I : Set G.rootBase.support) :
    IsClosedImmersion (leviInclusion G I).left :=
  closedSubgroupInclusion_isClosed G.coordinateAlgebra (G.leviIdeal I)

/-- The standard Levi inclusion preserves the group operation. -/
instance leviInclusion_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (leviInclusion G I) :=
  closedSubgroupInclusion_isMonHom G.coordinateAlgebra (G.leviIdeal I)

/-- Levi rational points identify with the selected-character centralizer point group. -/
def leviPointsMulEquiv (I : Set G.rootBase.support) :
    (leviVariety G I).points ≃* G.leviPoints I :=
  (closedSubgroupPointsMulEquiv G.coordinateAlgebra (G.leviIdeal I)).trans
    (MulEquiv.subgroupCongr (G.leviIdeal_points I))

/-- The Levi point identification agrees with the ambient group inclusion. -/
theorem leviInclusion_points (I : Set G.rootBase.support) (l : (leviVariety G I).points) :
    Variety.mapPoints (leviInclusion G I) l =
      reductivePointsMulEquiv G (leviPointsMulEquiv G I l) := by
  have hc : (leviPointsMulEquiv G I l : G.points) =
      (closedSubgroupPointsMulEquiv G.coordinateAlgebra (G.leviIdeal I) l : G.points) :=
    MulEquiv.subgroupCongr_apply (G.leviIdeal_points I) _
  exact (closedSubgroupInclusion_points G.coordinateAlgebra (G.leviIdeal I) l).trans
    (congrArg (affineGroupPointsMulEquiv K G.coordinateAlgebra) hc.symm)


end SchubertGeometry
