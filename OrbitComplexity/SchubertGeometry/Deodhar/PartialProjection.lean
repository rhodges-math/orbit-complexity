import OrbitComplexity.SchubertGeometry.Deodhar.CellParameterPoints

/-! # Intrinsic partial-flag interpretation of cell projections

The coordinate projection of an increasing cell extension preserves its rank-one
partial flag. Its value in the preceding cell is therefore uniquely determined.
-/

open CategoryTheory AlgebraicGeometry ReductiveGroups
namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))

/-- The additive product projection selects the preceding root-subgroup point. -/
theorem rankOneGaFirst_points (x : (rankOneGaProductVariety G w).points) :
    GroupActions.Variety.mapPoints (rankOneGaFirst G w) x =
      (rankOneGaProductPointsEquiv G w x).1 := by
  apply Subtype.ext
  exact (GroupActions.affineProductPointsEquiv_fst K _ _ x).symm

/-- The increasing-cell projection retains the first additive-product coordinate. -/
theorem rankOneGaProjection_points (x : (rankOneGaProductVariety G w).points) :
    GroupActions.Variety.mapPoints (rankOneCellProjection G w i hw)
      (GroupActions.Variety.mapPoints (rankOneGaCellIso G w i hw).hom x) =
        GroupActions.Variety.mapPoints (schubertCellIso G w).hom
          (rankOneGaProductPointsEquiv G w x).1 := by
  rw [← GroupActions.Variety.mapPoints_comp, rankOneGaCellIso_projection,
    GroupActions.Variety.mapPoints_comp, rankOneGaFirst_points]

/-- The projected flag is represented by the preceding root product and Weyl point. -/
theorem rankOneGaProjection_ambient (x : (rankOneGaProductVariety G w).points) :
    GroupActions.Variety.mapPoints (schubertCellInclusion G w)
      (GroupActions.Variety.mapPoints (rankOneCellProjection G w i hw)
        (GroupActions.Variety.mapPoints (rankOneGaCellIso G w i hw).hom x)) =
      flagVarietyPointsEquiv G (flagProjection G
        ((schubertUnipotentPointsEquiv G w (rankOneGaProductPointsEquiv G w x).1 : G.points) *
          G.weylPoint w)) := by
  rw [rankOneGaProjection_points, ← GroupActions.Variety.mapPoints_comp,
    schubertCellIso_hom_comp, schubertRootMorphism_points]
  rfl

/-- An additive root extension has the same partial flag as its preceding-cell projection. -/
theorem rankOnePartial_gaPoint (p : (schubertUnipotent G w).points) (t : K) :
    let x := (rankOneGaProductPointsEquiv G w).symm
      (p, GroupActions.additivePointsEquiv K t)
    rankOnePartialProjection G i ((flagVarietyPointsEquiv G).symm
      (GroupActions.Variety.mapPoints
        ((rankOneGaCellIso G w i hw).hom ≫ schubertCellInclusion G
          (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) x)) =
      rankOnePartialProjection G i ((flagVarietyPointsEquiv G).symm
        (GroupActions.Variety.mapPoints (schubertCellInclusion G w)
          (GroupActions.Variety.mapPoints (rankOneCellProjection G w i hw)
            (GroupActions.Variety.mapPoints (rankOneGaCellIso G w i hw).hom x)))) := by
  let x := (rankOneGaProductPointsEquiv G w).symm
    (p, GroupActions.additivePointsEquiv K t)
  let z := GroupActions.Variety.mapPoints (rankOneGaCellIso G w i hw).hom x
  let u : G.points := schubertUnipotentPointsEquiv G w p
  let Ψ : (flagVariety G).points → G.points ⧸ rankOneParabolicPoints G i :=
    fun q => rankOnePartialProjection G i ((flagVarietyPointsEquiv G).symm q)
  have hl := congrArg Ψ (rankOneGaCellIso_ambient_points G w i hw p t)
  have hr := congrArg Ψ (rankOneGaProjection_ambient G w i hw x)
  have hleft : Ψ (GroupActions.Variety.mapPoints
      ((rankOneGaCellIso G w i hw).hom ≫ schubertCellInclusion G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) x) =
      rankOnePartialProjection G i (flagProjection G
        (u * G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t *
          (G.reflectionPoint i.val)⁻¹)) := by
    simpa only [Ψ, Equiv.symm_apply_apply] using hl
  have hright : Ψ (GroupActions.Variety.mapPoints (schubertCellInclusion G w)
      (GroupActions.Variety.mapPoints (rankOneCellProjection G w i hw) z)) =
        rankOnePartialProjection G i (flagProjection G (u * G.weylPoint w)) := by
    simpa only [Ψ, x, z, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using hr
  have hpart : rankOnePartialProjection G i (flagProjection G
      (u * G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t *
        (G.reflectionPoint i.val)⁻¹)) =
      rankOnePartialProjection G i (flagProjection G (u * G.weylPoint w)) := by
    apply Eq.symm
    apply (rankOnePartialProjection_eq G i _ _).mpr
    have hm : gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹ ∈
        rankOneParabolicPoints G i :=
      (rankOneParabolicPoints G i).mul_mem
        (Or.inl ((G.isBruhatSystem.rankOne i).x_mem t))
        (Or.inr (G.isBruhatSystem.rankOne i).inv_mem_doubleCoset)
    have he : (u * G.weylPoint w)⁻¹ *
        (u * G.weylPoint w * gaParameterPoint (G.simpleRootMap i) t *
          (G.reflectionPoint i.val)⁻¹) =
        gaParameterPoint (G.simpleRootMap i) t * (G.reflectionPoint i.val)⁻¹ := by group
    rw [he]
    exact hm
  exact hleft.trans (hpart.trans hright.symm)

private theorem forall_equiv_product {A B C D E : Type*} (e : A ≃ B × C)
    (f : D ≃ C) (g : A ≃ E) (P : E → Prop)
    (h : ∀ b d, P (g (e.symm (b, f d)))) : ∀ z, P z := by
  intro z
  obtain ⟨x, hx⟩ := g.surjective z
  obtain ⟨p, hp⟩ := e.symm.surjective x
  obtain ⟨d, hd⟩ := f.surjective p.2
  have hh := h p.1 d
  rw [hd, Prod.mk.eta, hp, hx] at hh
  exact hh

/-- The increasing-cell projection preserves the rank-one partial flag on all rational points. -/
theorem rankOnePartial_projection
    (z : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).points) :
    rankOnePartialProjection G i ((flagVarietyPointsEquiv G).symm
      (GroupActions.Variety.mapPoints (schubertCellInclusion G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) z)) =
      rankOnePartialProjection G i ((flagVarietyPointsEquiv G).symm
        (GroupActions.Variety.mapPoints (schubertCellInclusion G w)
          (GroupActions.Variety.mapPoints (rankOneCellProjection G w i hw) z))) := by
  let P : (schubertCell G
      (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).points → Prop := fun y =>
    rankOnePartialProjection G i ((flagVarietyPointsEquiv G).symm
      (GroupActions.Variety.mapPoints (schubertCellInclusion G
        (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) y)) =
      rankOnePartialProjection G i ((flagVarietyPointsEquiv G).symm
        (GroupActions.Variety.mapPoints (schubertCellInclusion G w)
          (GroupActions.Variety.mapPoints (rankOneCellProjection G w i hw) y)))
  change P z
  refine forall_equiv_product (rankOneGaProductPointsEquiv G w)
    (GroupActions.additivePointsEquiv K)
    (GroupActions.Variety.pointsHomeomorph (rankOneGaCellIso G w i hw)).toEquiv P ?_ z
  intro p t
  let x := (rankOneGaProductPointsEquiv G w).symm
    (p, GroupActions.additivePointsEquiv K t)
  have hc := GroupActions.Variety.mapPoints_comp (rankOneGaCellIso G w i hw).hom
    (schubertCellInclusion G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)) x
  exact (congrArg (fun q => rankOnePartialProjection G i
    ((flagVarietyPointsEquiv G).symm q)) hc.symm).trans (rankOnePartial_gaPoint G w i hw p t)

end
end SchubertGeometry
