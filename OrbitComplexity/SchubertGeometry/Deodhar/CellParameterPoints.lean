import OrbitComplexity.SchubertGeometry.Deodhar.CellTrivialization
import OrbitComplexity.SchubertGeometry.Deodhar.RepresentativeFlags
import OrbitComplexity.SchubertGeometry.Deodhar.PartialFlagPoints

/-! # Flags in additive-line cell charts

The multiplication chart sends its additive coordinate to the chosen simple-root point
followed by the inverse simple representative.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))

/-- Multiplication identifies the two root factors with the extended inversion subgroup. -/
abbrev rankOneRootIso : (rankOneProductVariety G w i hw).toOver ≅
    (schubertUnipotent G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver :=
  GroupActions.rootProductIso G _ _ _
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase _)
    (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
    (rankOneRoot_closed G w i hw) (rankOneRoot_union G w i hw)
    (rankOneRoot_disjoint G w i)

/-- Rational points of a rank-one root product are pairs of its root-subgroup points. -/
abbrev rankOneProductPointsEquiv := GroupActions.rootProductPointsEquiv G
  (leftRootInversionIndices G.rootBase w) (rankOneRootSet G w i)
  (LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
  (rankOneRoot_closed G w i hw)

private abbrev secondRootPoint (p : (GroupActions.rootSubsetVariety G
    (rankOneRootSet G w i) (rankOneRoot_closed G w i hw)).points) : G.points :=
  GroupActions.rootSubsetPointsMulEquiv G _ (rankOneRoot_closed G w i hw) p

/-- The root-product isomorphism multiplies the two ambient group values. -/
theorem rankOneRootIso_values (x : (rankOneProductVariety G w i hw).points) :
    (schubertUnipotentPointsEquiv G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)
      (GroupActions.Variety.mapPoints (rankOneRootIso G w i hw).hom x) : G.points) =
      (schubertUnipotentPointsEquiv G w (rankOneProductPointsEquiv G w i hw x).1 : G.points) *
        secondRootPoint G w i hw (rankOneProductPointsEquiv G w i hw x).2 := by
  let v := w * RootPairing.weylGroup.ofIdx G.rootSystem i
  let hV := LeftRootInversionIndices.isPositiveRootClosed G.rootBase v
  let hW := LeftRootInversionIndices.isPositiveRootClosed G.rootBase w
  let hS := rankOneRoot_closed G w i hw
  let y := GroupActions.Variety.mapPoints (rankOneRootIso G w i hw).hom x
  have hi : GroupActions.Variety.mapPoints (schubertUnipotentInclusion G v) y =
      GroupActions.reductivePointsEquiv G (schubertUnipotentPointsEquiv G v y) :=
    GroupActions.rootSubsetInclusion_points G (leftRootInversionIndices G.rootBase v) hV y
  have hc := GroupActions.rootProductIso_points G
    (leftRootInversionIndices G.rootBase v) (leftRootInversionIndices G.rootBase w)
    (rankOneRootSet G w i) hV hW hS (rankOneRoot_union G w i hw)
    (rankOneRoot_disjoint G w i) x
  apply (GroupActions.reductivePointsEquiv G).injective
  exact hi.symm.trans ((GroupActions.Variety.mapPoints_comp
    (rankOneRootIso G w i hw).hom (schubertUnipotentInclusion G v) x).symm.trans hc)

/-- The root-product cell chart agrees with the inversion-root map into the flag variety. -/
theorem rankOneCellIso_comp :
    (rankOneCellIso G w i hw).hom ≫ schubertCellInclusion G
      (w * RootPairing.weylGroup.ofIdx G.rootSystem i) =
      (rankOneRootIso G w i hw).hom ≫ schubertRootMorphism G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i) := by
  dsimp only [rankOneCellIso, Iso.trans_hom]
  rw [Category.assoc, schubertCellIso_hom_comp]

/-- A root-product cell point is represented by its two root values and final Weyl point. -/
theorem rankOneCellIso_ambient_points (x : (rankOneProductVariety G w i hw).points) :
    GroupActions.Variety.mapPoints
      ((rankOneCellIso G w i hw).hom ≫ schubertCellInclusion G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) x =
      flagVarietyPointsEquiv G (flagProjection G
        (((schubertUnipotentPointsEquiv G w
          (rankOneProductPointsEquiv G w i hw x).1 : G.points) *
          secondRootPoint G w i hw (rankOneProductPointsEquiv G w i hw x).2) *
          G.weylPoint (w * RootPairing.weylGroup.ofIdx G.rootSystem i))) := by
  let v := w * RootPairing.weylGroup.ofIdx G.rootSystem i
  let y := GroupActions.Variety.mapPoints (rankOneRootIso G w i hw).hom x
  have hc := congrArg (fun f : (rankOneProductVariety G w i hw).toOver ⟶
      (flagVariety G).toOver => GroupActions.Variety.mapPoints f x)
        (rankOneCellIso_comp G w i hw)
  have hm := GroupActions.Variety.mapPoints_comp (rankOneRootIso G w i hw).hom
    (schubertRootMorphism G v) x
  have hp := schubertRootMorphism_points G v y
  have hv := congrArg (fun g : G.points => flagVarietyPointsEquiv G
    (flagProjection G (g * G.weylPoint v))) (rankOneRootIso_values G w i hw x)
  exact hc.trans (hm.trans (hp.trans hv))


/-- The additive cell chart is the root-product chart after its additive root isomorphism. -/
theorem rankOneGaCellIso_comp :
    (rankOneGaCellIso G w i hw).hom ≫ schubertCellInclusion G
      (w * RootPairing.weylGroup.ofIdx G.rootSystem i) =
        (rankOneGaProductIso G w i hw).hom ≫
          ((rankOneCellIso G w i hw).hom ≫ schubertCellInclusion G
            (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) := Category.assoc _ _ _

private theorem inverseSimple_rootProduct (u : G.points) (t : K) :
    flagProjection G
      (u * (G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t * (G.weylPoint w)⁻¹) *
        G.weylPoint (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) =
      flagProjection G (u * G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t *
        (G.reflectionPoint i.val)⁻¹) := by
  let a : G.points := u *
    (G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t * (G.weylPoint w)⁻¹)
  have h := congrArg (fun q : flagPoints G => a • q) (inverseSimple_flag G w i).symm
  change flagProjection G (a * G.weylPoint
    (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) =
      flagProjection G (a * (G.weylPoint w * (G.reflectionPoint i.val)⁻¹)) at h
  have hm : a * (G.weylPoint w * (G.reflectionPoint i.val)⁻¹) =
      u * G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t *
        (G.reflectionPoint i.val)⁻¹ := by
    dsimp only [a]
    group
  exact h.trans (congrArg (flagProjection G) hm)

/-- The additive cell coordinate has the chosen root parameter and inverse simple representative. -/
theorem rankOneGaCellIso_ambient_points (p : (schubertUnipotent G w).points) (t : K) :
    GroupActions.Variety.mapPoints
      ((rankOneGaCellIso G w i hw).hom ≫ schubertCellInclusion G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i))
      ((rankOneGaProductPointsEquiv G w).symm (p, GroupActions.additivePointsEquiv K t)) =
      flagVarietyPointsEquiv G (flagProjection G
        ((schubertUnipotentPointsEquiv G w p : G.points) *
          G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t *
          (G.reflectionPoint i.val)⁻¹)) := by
  let x := (rankOneGaProductPointsEquiv G w).symm
    (p, GroupActions.additivePointsEquiv K t)
  have hpair : rankOneProductPointsEquiv G w i hw
      (GroupActions.Variety.mapPoints (rankOneGaProductIso G w i hw).hom x) =
        (p, GroupActions.Variety.mapPoints (rankOneGaIso G w i hw).hom
          (GroupActions.additivePointsEquiv K t)) := by
    rw [rankOneGaProductIso_points]
    simp only [x, Equiv.apply_symm_apply]
  let y := GroupActions.Variety.mapPoints (rankOneGaProductIso G w i hw).hom x
  have hc := congrArg (fun f : (rankOneGaProductVariety G w).toOver ⟶
      (flagVariety G).toOver => GroupActions.Variety.mapPoints f x)
        (rankOneGaCellIso_comp G w i hw)
  have hm := GroupActions.Variety.mapPoints_comp (rankOneGaProductIso G w i hw).hom
    ((rankOneCellIso G w i hw).hom ≫ schubertCellInclusion G
      (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) x
  have hp := rankOneCellIso_ambient_points G w i hw y
  rw [hpair] at hp
  have hcoord := congrArg (fun v : G.points => flagVarietyPointsEquiv G (flagProjection G
    ((schubertUnipotentPointsEquiv G w p : G.points) * v *
      G.weylPoint (w * RootPairing.weylGroup.ofIdx G.rootSystem i))))
        (rankOneGaIso_points G w i hw t)
  have hflag := congrArg (flagVarietyPointsEquiv G) (inverseSimple_rootProduct G w i
    (schubertUnipotentPointsEquiv G w p) t)
  exact hc.trans (hm.trans (hp.trans (hcoord.trans hflag)))

end
end SchubertGeometry
