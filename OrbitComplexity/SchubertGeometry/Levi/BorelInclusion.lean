import OrbitComplexity.SchubertGeometry.Levi.Subgroup
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupLeviInclusions
import OrbitComplexity.SchubertGeometry.Levi.Schubert
import OrbitComplexity.GroupActions.Varieties.ClosedSubgroupMaps

/-! # The Levi--Borel inclusion into the Levi

The nested coordinate ideals give the closed group inclusion.
Its ambient square identifies restriction of the Levi action with the Levi--Borel action.
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

private theorem leviReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (G.leviIdeal I).toIdeal) := by
  change IsReduced (G.leviAlgebra I)
  infer_instance

private theorem borelReduced (I : Set G.rootBase.support) :
    IsReduced (G.coordinateAlgebra ⧸ (G.leviBorelIdeal I).toIdeal) := by
  change IsReduced (G.leviBorelAlgebra I)
  infer_instance

attribute [local instance] coordinateReduced leviReduced borelReduced

/-- The Levi--Borel intersection includes as a closed subgroup of the Levi variety. -/
def leviBorelLeviInclusion (I : Set G.rootBase.support) :
    (leviBorelVariety G I).toOver ⟶ (leviVariety G I).toOver :=
  closedSubgroupMap G.coordinateAlgebra (G.leviIdeal I) (G.leviBorelIdeal I)
    (G.leviIdeal_le_leviBorel I)

/-- The inclusion of the Levi--Borel subgroup in the Levi is closed. -/
instance leviBorelLeviInclusion_isClosed (I : Set G.rootBase.support) :
    IsClosedImmersion (leviBorelLeviInclusion G I).left :=
  closedSubgroupMap_isClosed _ _ _ _

/-- The inclusion of the Levi--Borel subgroup in the Levi preserves multiplication. -/
instance leviBorelLeviInclusion_isMonHom (I : Set G.rootBase.support) :
    IsMonHom (leviBorelLeviInclusion G I) :=
  closedSubgroupMap_isMonHom _ _ _ _

/-- Composing the Levi--Borel inclusion with the Levi inclusion gives its ambient inclusion. -/
@[reassoc]
theorem leviBorelLeviInclusion_comp (I : Set G.rootBase.support) :
    leviBorelLeviInclusion G I ≫ leviInclusion G I = leviBorelInclusion G I :=
  closedSubgroupMap_comp_inclusion _ _ _ _

/-- The inclusion into the Levi preserves the Levi--Borel point in the ambient group. -/
theorem leviBorelLeviInclusion_points (I : Set G.rootBase.support)
    (b : (leviBorelVariety G I).points) :
    (leviPointsMulEquiv G I (Variety.mapPoints (leviBorelLeviInclusion G I) b) : G.points) =
      (leviBorelPointsMulEquiv G I b : G.points) := by
  have he : Variety.mapPoints (leviInclusion G I)
      (Variety.mapPoints (leviBorelLeviInclusion G I) b) =
        Variety.mapPoints (leviBorelInclusion G I) b := by
    rw [← Variety.mapPoints_comp, leviBorelLeviInclusion_comp]
  rw [leviInclusion_points, leviBorelInclusion_points] at he
  exact (reductivePointsMulEquiv G).injective he

/-- The Levi action on flags restricts to the Levi--Borel flag action. -/
theorem leviBorelLeviInclusion_smul (I : Set G.rootBase.support)
    (b : (leviBorelVariety G I).points) (q : (flagVariety G).points) :
    Variety.mapPoints (leviBorelLeviInclusion G I) b • q = b • q := by
  rw [leviFlag_smul, leviBorelFlag_smul, leviBorelLeviInclusion_points]

omit [IsAlgClosed K] [CharZero K] in
private theorem equivariant_mapPoints {H X Y : Variety K} [GrpObj H.toOver]
    [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (t : H.points) (x : X.points) :
    Variety.mapPoints f (t • x) = t • Variety.mapPoints f x := by
  apply Y.pointsEquivOverHom.injective
  change X.pointsEquivOverHom (t • x) ≫ f = Y.pointsEquivOverHom (t • Variety.mapPoints f x)
  rw [Variety.pointsEquivOverHom_smul, Variety.pointsEquivOverHom_smul]
  exact IsModHom.map_smul f (H.pointsEquivOverHom t) (X.pointsEquivOverHom x)

/-- Every equivariant Levi action on a Schubert variety restricts to its Levi--Borel action. -/
theorem leviBorelLevi_schubert_smul (I : Set G.rootBase.support) (w : G.weylGroup)
    [ModObj (leviVariety G I).toOver (schubertVariety G w).toOver]
    [IsModHom (leviVariety G I).toOver (schubertInclusion G w)]
    (b : (leviBorelVariety G I).points) (q : (schubertVariety G w).points) :
    Variety.mapPoints (leviBorelLeviInclusion G I) b • q = b • q := by
  apply Variety.mapPoints_injective_of_mono (schubertInclusion G w)
  rw [equivariant_mapPoints, leviBorelSchubert_smul, leviBorelLeviInclusion_smul]

end SchubertGeometry
