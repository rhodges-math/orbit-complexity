import OrbitComplexity.GroupActions.Varieties.ClosedSubgroup
import OrbitComplexity.GroupActions.Varieties.ReductiveVariety
import OrbitComplexity.SchubertGeometry.Parabolics.DoubleCosets
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing

/-! # Standard parabolic group varieties

The vanishing Hopf ideal of the closed standard parabolic point group defines a reduced
affine subgroup variety. Its rational points agree with the prescribed parabolic subgroup.
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

private def parabolicIdeal (I : Set G.rootBase.support) : HopfIdeal K G.coordinateAlgebra :=
  HopfIdeal.vanishingIdeal (standardParabolicPoints G I)

private theorem parabolicIdeal_points (I : Set G.rootBase.support) :
    CommHopfAlgCat.quotientPointsSubgroup (CommHopfAlgCat.of K G.coordinateAlgebra)
      (parabolicIdeal G I) (CommAlgCat.of K K) = standardParabolicPoints G I := by
  obtain ⟨S, hS⟩ := (pointGroup_isClosed_iff
    (standardParabolicPoints G I : Set G.points)).mp (standardParabolicPoints_bruhat G I).2
  apply le_antisymm
  · intro x hx
    change x ∈ (standardParabolicPoints G I : Set G.points)
    rw [hS]
    intro f hf
    have hvanish : f ∈ parabolicIdeal G I := by
      apply (HopfIdeal.mem_vanishingIdeal (standardParabolicPoints G I) f).mpr
      intro g
      have hg : g.val ∈ (standardParabolicPoints G I : Set G.points) := g.property
      rw [hS] at hg
      exact hg f hf
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff
      (CommHopfAlgCat.of K G.coordinateAlgebra) (parabolicIdeal G I) (CommAlgCat.of K K) x).mp
        hx f hvanish
  · exact (HopfIdeal.le_vanishingIdeal_iff (standardParabolicPoints G I)
      (parabolicIdeal G I)).mp le_rfl

private theorem parabolicReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (parabolicIdeal G I).toIdeal) := by
  change IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K G.coordinateAlgebra)
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)))
  infer_instance
attribute [local instance] parabolicReduced

/-- The reduced standard parabolic subgroup as an affine group variety. -/
def standardParabolicVariety (I : Set G.rootBase.support) : Variety K :=
  closedSubgroupVariety G.coordinateAlgebra (parabolicIdeal G I)

/-- The standard parabolic variety is a group object. -/
instance standardParabolicVarietyGroup (I : Set G.rootBase.support) :
    GrpObj (standardParabolicVariety G I).toOver :=
  closedSubgroupVarietyGroup G.coordinateAlgebra (parabolicIdeal G I)

/-- The standard parabolic variety includes into the reductive group. -/
def standardParabolicInclusion (I : Set G.rootBase.support) :
    (standardParabolicVariety G I).toOver ⟶ (reductiveVariety G).toOver :=
  closedSubgroupInclusion G.coordinateAlgebra (parabolicIdeal G I)

/-- The standard parabolic inclusion is a closed immersion. -/
instance parabolicInclusion_isClosed (I : Set G.rootBase.support) :
    IsClosedImmersion (standardParabolicInclusion G I).left :=
  closedSubgroupInclusion_isClosed G.coordinateAlgebra (parabolicIdeal G I)

/-- The standard parabolic inclusion preserves the group operation. -/
instance parabolicInclusion_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (standardParabolicInclusion G I) :=
  closedSubgroupInclusion_isMonHom G.coordinateAlgebra (parabolicIdeal G I)

/-- Rational parabolic points identify with the standard parabolic point subgroup. -/
def parabolicPointsMulEquiv (I : Set G.rootBase.support) :
    (standardParabolicVariety G I).points ≃* standardParabolicPoints G I :=
  (closedSubgroupPointsMulEquiv G.coordinateAlgebra (parabolicIdeal G I)).trans
    (MulEquiv.subgroupCongr (parabolicIdeal_points G I))

/-- The parabolic point identification agrees with the reductive group inclusion. -/
theorem parabolicInclusion_points (I : Set G.rootBase.support)
    (p : (standardParabolicVariety G I).points) :
    Variety.mapPoints (standardParabolicInclusion G I) p =
      reductivePointsMulEquiv G (parabolicPointsMulEquiv G I p) := by
  have hc : (parabolicPointsMulEquiv G I p : G.points) =
      (closedSubgroupPointsMulEquiv G.coordinateAlgebra (parabolicIdeal G I) p : G.points) :=
    MulEquiv.subgroupCongr_apply (parabolicIdeal_points G I) _
  exact (closedSubgroupInclusion_points G.coordinateAlgebra (parabolicIdeal G I) p).trans
    (congrArg (affineGroupPointsMulEquiv K G.coordinateAlgebra) hc.symm)

end SchubertGeometry
