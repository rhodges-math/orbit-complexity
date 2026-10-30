import OrbitComplexity.SchubertGeometry.Deodhar.FlagLifts
import OrbitComplexity.SchubertGeometry.Cells.CellChart
import OrbitComplexity.GroupActions.Actions.RightTranslations

/-! # Regular group-valued lifts of Schubert cells

An inversion-root coordinate times its Weyl representative gives a regular lift of the
Schubert cell to the reductive group. Any other regular lift differs by a regular Borel factor.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private def rootLift (w : G.weylGroup) : (schubertUnipotent G w).toOver ⟶
    (GroupActions.reductiveVariety G).toOver :=
  schubertUnipotentInclusion G w ≫ (GroupActions.rightTranslation
    (GroupActions.reductiveVariety G) (GroupActions.reductivePointsEquiv G (G.weylPoint w))).hom

private theorem rootLift_points (w : G.weylGroup) (p : (schubertUnipotent G w).points) :
    GroupActions.Variety.mapPoints (rootLift G w) p = GroupActions.reductivePointsEquiv G
      ((schubertUnipotentPointsEquiv G w p : G.points) * G.weylPoint w) := by
  let e := GroupActions.reductivePointsMulEquiv G
  let u : G.points := schubertUnipotentPointsEquiv G w p
  have hi : GroupActions.Variety.mapPoints (schubertUnipotentInclusion G w) p = e u :=
    GroupActions.rootSubsetInclusion_points G _
      (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w) p
  have hc := GroupActions.Variety.mapPoints_comp (schubertUnipotentInclusion G w)
    (GroupActions.rightTranslation (GroupActions.reductiveVariety G) (e (G.weylPoint w))).hom p
  have hr := GroupActions.rightTranslation_points (GroupActions.reductiveVariety G)
    (e (G.weylPoint w)) (GroupActions.Variety.mapPoints (schubertUnipotentInclusion G w) p)
  exact hc.trans (hr.trans ((congrArg (fun h => h * e (G.weylPoint w)) hi).trans
    (map_mul e u (G.weylPoint w)).symm))

private theorem rootLift_quotient (w : G.weylGroup) :
    rootLift G w ≫ flagQuotientMorphism G = schubertRootMorphism G w := by
  apply GroupActions.Variety.mapPoints_injective
  funext p
  have hc := GroupActions.Variety.mapPoints_comp (rootLift G w) (flagQuotientMorphism G) p
  have hp := congrArg (GroupActions.Variety.mapPoints (flagQuotientMorphism G))
    (rootLift_points G w p)
  have hq := flagQuotientMorphism_points G
    ((schubertUnipotentPointsEquiv G w p : G.points) * G.weylPoint w)
  exact hc.trans (hp.trans (hq.trans (schubertRootMorphism_points G w p).symm))

/-- The regular group-valued lift of a Schubert cell given by its inversion-root coordinates. -/
def schubertCellLift (w : G.weylGroup) : (schubertCell G w).toOver ⟶
    (GroupActions.reductiveVariety G).toOver :=
  (schubertCellIso G w).inv ≫ rootLift G w

/-- The canonical group-valued cell lift projects to the cell inclusion. -/
theorem schubertCellLift_quotient (w : G.weylGroup) :
    schubertCellLift G w ≫ flagQuotientMorphism G = schubertCellInclusion G w := by
  let e := schubertCellIso G w
  have hr := rootLift_quotient G w
  have he := schubertCellIso_hom_comp G w
  exact (Category.assoc e.inv (rootLift G w) (flagQuotientMorphism G)).trans
    ((congrArg (fun f => e.inv ≫ f) hr).trans
      ((congrArg (fun f => e.inv ≫ f) he.symm).trans (e.inv_hom_id_assoc _)))

/-- The canonical cell lift represents a flag by its inversion-root point times its Weyl point. -/
theorem schubertCellLift_points (w : G.weylGroup) (z : (schubertCell G w).points) :
    GroupActions.Variety.mapPoints (schubertCellLift G w) z = GroupActions.reductivePointsEquiv G
      ((schubertUnipotentPointsEquiv G w
        (GroupActions.Variety.mapPoints (schubertCellIso G w).inv z) : G.points) *
          G.weylPoint w) :=
  (GroupActions.Variety.mapPoints_comp (schubertCellIso G w).inv (rootLift G w) z).trans
    (rootLift_points G w _)

private theorem cellLift_flags (w : G.weylGroup) (X : GroupActions.Variety K)
    (f : X.toOver ⟶ (schubertCell G w).toOver)
    (g : X.toOver ⟶ (GroupActions.reductiveVariety G).toOver)
    (hg : g ≫ flagQuotientMorphism G = f ≫ schubertCellInclusion G w) :
    (f ≫ schubertCellLift G w) ≫ flagQuotientMorphism G = g ≫ flagQuotientMorphism G :=
  (Category.assoc f (schubertCellLift G w) (flagQuotientMorphism G)).trans
    ((congrArg (fun m => f ≫ m) (schubertCellLift_quotient G w)).trans hg.symm)

/-- The regular Borel factor comparing a flag lift with its canonical Schubert-cell lift. -/
def schubertBorelLift (w : G.weylGroup) (X : GroupActions.Variety K)
    (f : X.toOver ⟶ (schubertCell G w).toOver)
    (g : X.toOver ⟶ (GroupActions.reductiveVariety G).toOver)
    (hg : g ≫ flagQuotientMorphism G = f ≫ schubertCellInclusion G w) :
    X.toOver ⟶ (GroupActions.borelVariety G).toOver :=
  borelDifference G X (f ≫ schubertCellLift G w) g (cellLift_flags G w X f g hg)

/-- Multiplying the canonical cell lift by its Borel factor recovers the specified group lift. -/
theorem schubertBorelLift_mul (w : G.weylGroup) (X : GroupActions.Variety K)
    (f : X.toOver ⟶ (schubertCell G w).toOver)
    (g : X.toOver ⟶ (GroupActions.reductiveVariety G).toOver)
    (hg : g ≫ flagQuotientMorphism G = f ≫ schubertCellInclusion G w) :
    (f ≫ schubertCellLift G w) *
      (schubertBorelLift G w X f g hg ≫ GroupActions.borelInclusion G) = g :=
  borelDifference_mul G X (f ≫ schubertCellLift G w) g (cellLift_flags G w X f g hg)

end
end SchubertGeometry
