import OrbitComplexity.SchubertGeometry.Deodhar.RootParameter
import OrbitComplexity.SchubertGeometry.Deodhar.RepresentativeFlags
import OrbitComplexity.SchubertGeometry.Deodhar.RankOnePoints

/-! # The specified additive coordinate on a simple cell

The fixed positive simple-root parameter identifies the additive line with the simple
Schubert cell. Its flag representative is the inverse of the chosen simple reflection point.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups TauCeti
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (i : G.rootBase.support)

private theorem simpleClosed : IsPositiveRootClosed G.rootBase {(i : G.rootIndex)} := by
  rw [← leftRootInversionIndices_simple G.rootBase i]
  exact LeftRootInversionIndices.isPositiveRootClosed G.rootBase _

private theorem simpleKills : ∀ b ∈ G.rootSubsetIdeal {(i : G.rootIndex)} (simpleClosed G i),
    gaAffineGroupTangent (G.simpleRootMap i) b = 0 := by
  apply (tangent_mem_hopfQuotient_iff _ _).mp
  change gaAffineGroupTangent (G.simpleRootMap i) ∈
    (hopfTangentImage (G.rootSubsetIdeal {(i : G.rootIndex)} (simpleClosed G i))).toSubmodule
  rw [G.singletonRootTangent _ (G.rootBase.isPos_of_mem_support i.property)]
  exact G.simpleRootMap_tangent_mem i

private def supportIso (R S : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (hS : IsPositiveRootClosed G.rootBase S)
    (h : R = S) : (GroupActions.rootSubsetVariety G R hR).toOver ≅
      (GroupActions.rootSubsetVariety G S hS).toOver := by
  subst S
  exact Iso.refl _

private theorem supportIso_comp (R S : Set G.rootIndex)
    (hR : IsPositiveRootClosed G.rootBase R) (hS : IsPositiveRootClosed G.rootBase S)
    (h : R = S) : (supportIso G R S hR hS h).hom ≫ GroupActions.rootSubsetInclusion G S hS =
      GroupActions.rootSubsetInclusion G R hR := by
  subst S
  exact Category.id_comp _

/-- The specified positive simple-root map identifies Ga with the simple inversion subgroup. -/
def simpleRootIso : (GroupActions.additiveVariety K).toOver ≅
    (schubertUnipotent G (RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver :=
  GroupActions.rootLineIso G i.val (G.rootBase.isPos_of_mem_support i.property)
    (simpleClosed G i) (G.simpleRootMap i) (simpleKills G i)
    (G.simpleRootMap_tangent_ne_zero i) ≪≫ supportIso G {(i : G.rootIndex)}
      (leftRootInversionIndices G.rootBase (RootPairing.weylGroup.ofIdx G.rootSystem i))
      (simpleClosed G i) (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)
      (leftRootInversionIndices_simple G.rootBase i).symm

/-- The simple root-line isomorphism retains the specified additive morphism into the group. -/
theorem simpleRootIso_inclusion :
    (simpleRootIso G i).hom ≫ schubertUnipotentInclusion G
      (RootPairing.weylGroup.ofIdx G.rootSystem i) =
        GroupActions.gaMorphism G (G.simpleRootMap i) := by
  change (_ ≫ (supportIso G _ _ _ _ _).hom) ≫ GroupActions.rootSubsetInclusion G _ _ = _
  rw [Category.assoc, supportIso_comp]
  exact GroupActions.rootLineIso_hom_comp G i.val
    (G.rootBase.isPos_of_mem_support i.property) (simpleClosed G i)
    (G.simpleRootMap i) (simpleKills G i) (G.simpleRootMap_tangent_ne_zero i)

/-- The specified positive simple-root parameter identifies Ga with the simple Schubert cell. -/
def simpleCellIso : (GroupActions.additiveVariety K).toOver ≅
    (schubertCell G (RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver :=
  simpleRootIso G i ≪≫ schubertCellIso G _

/-- The inverse simple reflection point represents the chosen simple Weyl flag. -/
theorem simpleRepresentative_flag :
    flagProjection G (G.reflectionPoint i.val)⁻¹ =
      flagProjection G (G.weylPoint (RootPairing.weylGroup.ofIdx G.rootSystem i)) := by
  have h := inverseSimple_flag G 1 i
  rw [G.weylPoint_eq, weylElementPoint_one, one_mul, one_mul] at h
  exact h

/-- The simple-cell chart is the specified additive map followed by the Weyl orbit morphism. -/
theorem simpleCellIso_comp : (simpleCellIso G i).hom ≫ schubertCellInclusion G
    (RootPairing.weylGroup.ofIdx G.rootSystem i) =
      GroupActions.gaMorphism G (G.simpleRootMap i) ≫
        GroupActions.Variety.orbitMorphism (GroupActions.reductiveVariety G)
          (flagVariety G) (weylFlagPoint G (RootPairing.weylGroup.ofIdx G.rootSystem i)) := by
  let s := RootPairing.weylGroup.ofIdx G.rootSystem i
  let e := simpleRootIso G i
  let j := schubertUnipotentInclusion G s
  let o := GroupActions.Variety.orbitMorphism (GroupActions.reductiveVariety G)
    (flagVariety G) (weylFlagPoint G s)
  have hcell : (schubertCellIso G s).hom ≫ schubertCellInclusion G s = j ≫ o :=
    schubertCellIso_hom_comp G s
  have hroot : e.hom ≫ j = GroupActions.gaMorphism G (G.simpleRootMap i) :=
    simpleRootIso_inclusion G i
  exact (Category.assoc e.hom (schubertCellIso G s).hom (schubertCellInclusion G s)).trans
    ((congrArg (fun m => e.hom ≫ m) hcell).trans
      ((Category.assoc e.hom j o).symm.trans (congrArg (fun m => m ≫ o) hroot)))

/-- The simple-cell additive parameter has flag representative x(t) times the inverse reflection. -/
theorem simpleCellIso_points (t : K) :
    GroupActions.Variety.mapPoints
      ((simpleCellIso G i).hom ≫ schubertCellInclusion G
        (RootPairing.weylGroup.ofIdx G.rootSystem i))
      (GroupActions.additivePointsEquiv K t) =
        flagVarietyPointsEquiv G (flagProjection G
          (gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹)) := by
  let s := RootPairing.weylGroup.ofIdx G.rootSystem i
  let p := GroupActions.additivePointsEquiv K t
  let m := GroupActions.gaMorphism G (G.simpleRootMap i)
  let o := GroupActions.Variety.orbitMorphism (GroupActions.reductiveVariety G)
    (flagVariety G) (weylFlagPoint G s)
  have he := congrArg (fun f => GroupActions.Variety.mapPoints f p) (simpleCellIso_comp G i)
  have hc := GroupActions.Variety.mapPoints_comp m o p
  have ho := GroupActions.Variety.mapPoints_orbitMorphism (GroupActions.reductiveVariety G)
    (flagVariety G) (weylFlagPoint G s) (GroupActions.Variety.mapPoints m p)
  have hp := congrArg (fun h : (GroupActions.reductiveVariety G).points =>
    h • weylFlagPoint G s) (GroupActions.gaMorphism_points G (G.simpleRootMap i) t)
  have ha := flagVarietyAction_points G (gaParameterPoint (G.simpleRootMap i) t)
    (flagProjection G (G.weylPoint s))
  have hq := congrArg (fun q => gaParameterPoint (G.simpleRootMap i) t • q)
    (simpleRepresentative_flag G i)
  exact he.trans (hc.trans (ho.trans (hp.trans
    (ha.trans (congrArg (flagVarietyPointsEquiv G) hq.symm)))))

end
end SchubertGeometry
