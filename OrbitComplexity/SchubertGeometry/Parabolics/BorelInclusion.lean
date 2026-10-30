import OrbitComplexity.SchubertGeometry.Parabolics.Subgroup
import OrbitComplexity.GroupActions.Varieties.ClosedSubgroupMaps
import OrbitComplexity.GroupActions.Varieties.BorelPoints
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

/-! # Borel inclusions into standard parabolics

Reduced point separation gives the reverse inclusion of defining Hopf ideals.
The resulting closed group morphism agrees with the ambient subgroup inclusions.
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

omit [CharZero K] in
private theorem borelReduced : IsReduced (G.coordinateAlgebra ⧸ G.borelIdeal.toIdeal) := by
  change IsReduced G.borelAlgebra
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  exact TauCeti.isReduced_of_smooth K G.borelAlgebra
attribute [local instance] borelReduced

private theorem parabolicReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸
      (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)).toIdeal) := by
  change IsReduced (CommHopfAlgCat.quotient (CommHopfAlgCat.of K G.coordinateAlgebra)
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)))
  infer_instance
attribute [local instance] parabolicReduced

private theorem parabolicIdeal_le_borel (I : Set G.rootBase.support) :
    HopfIdeal.vanishingIdeal (standardParabolicPoints G I) ≤ G.borelIdeal := by
  apply HopfIdeal.le_of_quotientPointsSubgroup_le
    (H := CommHopfAlgCat.of K G.coordinateAlgebra) (K := K)
  intro b hb
  apply (HopfIdeal.le_vanishingIdeal_iff (standardParabolicPoints G I)
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I))).mp le_rfl
  exact (le_sup_left : G.borelPoints ≤ standardParabolicPoints G I) hb

/-- The Borel includes as a closed subgroup of each standard parabolic variety. -/
def borelParabolicInclusion (I : Set G.rootBase.support) :
    (borelVariety G).toOver ⟶ (standardParabolicVariety G I).toOver :=
  closedSubgroupMap G.coordinateAlgebra (HopfIdeal.vanishingIdeal (standardParabolicPoints G I))
    G.borelIdeal (parabolicIdeal_le_borel G I)

/-- The Borel inclusion into a standard parabolic is a closed immersion. -/
instance borelParabolic_isClosed (I : Set G.rootBase.support) :
    IsClosedImmersion (borelParabolicInclusion G I).left :=
  closedSubgroupMap_isClosed G.coordinateAlgebra
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)) G.borelIdeal
      (parabolicIdeal_le_borel G I)

/-- The Borel inclusion into a standard parabolic preserves multiplication. -/
instance borelParabolic_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (borelParabolicInclusion G I) :=
  closedSubgroupMap_isMonHom G.coordinateAlgebra
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)) G.borelIdeal
      (parabolicIdeal_le_borel G I)

/-- The Borel-to-parabolic inclusion agrees with both ambient group inclusions. -/
theorem borelParabolic_comp (I : Set G.rootBase.support) :
    borelParabolicInclusion G I ≫ standardParabolicInclusion G I = borelInclusion G :=
  closedSubgroupMap_comp_inclusion G.coordinateAlgebra
    (HopfIdeal.vanishingIdeal (standardParabolicPoints G I)) G.borelIdeal
      (parabolicIdeal_le_borel G I)

/-- On rational points the Borel-to-parabolic inclusion is the subgroup inclusion. -/
theorem borelParabolic_points (I : Set G.rootBase.support) (b : (borelVariety G).points) :
    (parabolicPointsMulEquiv G I (Variety.mapPoints (borelParabolicInclusion G I) b) : G.points) =
      borelPointsMulEquiv G b := by
  apply (reductivePointsMulEquiv G).injective
  calc
    _ = Variety.mapPoints (standardParabolicInclusion G I)
        (Variety.mapPoints (borelParabolicInclusion G I) b) :=
      (parabolicInclusion_points G I _).symm
    _ = Variety.mapPoints (borelInclusion G) b := by
      rw [← Variety.mapPoints_comp, borelParabolic_comp G I]
    _ = _ := borelInclusion_points G b

end SchubertGeometry
