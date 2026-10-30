import OrbitComplexity.SchubertGeometry.FlagVariety.ActionCompatibility

/-! # The morphism acting on the flag variety

Compatible local multiplication morphisms glue over the group times flag variety.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private def actionSchemeHom : (flagActionProduct G).scheme ⟶ (flagVariety G).scheme :=
  (flagActionCover G).glueMorphisms (fun g => (flagActionChartMorphism G g).left)
    (fun g h => flagActionChart_compatible G g h)

private theorem actionSchemeHom_chart (g : G.points) :
    (flagActionChartFst G g).left ≫ actionSchemeHom G =
      (flagActionChartMorphism G g).left :=
  (flagActionCover G).ι_glueMorphisms _ _ g

private theorem actionSchemeHom_toSpec :
    actionSchemeHom G ≫ (flagVariety G).toSpec = (flagActionProduct G).toSpec := by
  apply (flagActionCover G).hom_ext
  intro g
  change G.points at g
  change (flagActionChartFst G g).left ≫
      (actionSchemeHom G ≫ (flagVariety G).toSpec) =
    (flagActionChartFst G g).left ≫ (flagActionProduct G).toSpec
  rw [← Category.assoc, actionSchemeHom_chart]
  exact (flagActionChartMorphism G g).w.trans (flagActionChartFst G g).w.symm

/-- The action morphism on the flag variety is glued from unipotent representatives. -/
def flagActionMorphism : (flagActionProduct G).toOver ⟶ (flagVariety G).toOver :=
  Over.homMk (actionSchemeHom G) (actionSchemeHom_toSpec G)

/-- The global action restricts to the local multiplication formula on every chart. -/
theorem flagActionChart_action (g : G.points) :
    flagActionChartFst G g ≫ flagActionMorphism G = flagActionChartMorphism G g := by
  apply Over.OverMorphism.ext
  exact actionSchemeHom_chart G g

private theorem actionPoint_chart (p : (flagActionProduct G).points) :
    ∃ (g : G.points) (x : (flagActionChartVariety G g).points),
      GroupActions.Variety.mapPoints (flagActionChartFst G g) x = p := by
  obtain ⟨g, l, hl⟩ := GroupActions.point_factors_openCover (flagActionCover G) p.val
  change G.points at g
  change Spec (CommRingCat.of K) ⟶ (flagActionChartVariety G g).scheme at l
  change l ≫ (flagActionChartFst G g).left = p.val at hl
  refine ⟨g, ⟨l, ?_⟩, Subtype.ext hl⟩
  have hi : (flagActionChartFst G g).left ≫ (flagActionProduct G).toSpec =
      (flagActionChartVariety G g).toSpec := (flagActionChartFst G g).w
  rw [← hi, ← Category.assoc, hl]
  exact p.property

/-- The global action morphism induces left multiplication on rational Borel cosets. -/
theorem flagActionMorphism_points (p : (flagActionProduct G).points) :
    GroupActions.Variety.mapPoints (flagActionMorphism G) p =
      flagVarietyPointsEquiv G
        ((GroupActions.reductivePointsMulEquiv G).symm
          (GroupActions.Variety.mapPoints (flagActionFst G) p) •
            (flagVarietyPointsEquiv G).symm
              (GroupActions.Variety.mapPoints (flagActionSnd G) p)) := by
  obtain ⟨g, x, rfl⟩ := actionPoint_chart G p
  rw [← GroupActions.Variety.mapPoints_comp, flagActionChart_action,
    flagActionChartMorphism_points]
  simp only [GroupActions.Variety.mapPoints_comp]
  have he := flagActionChart_flag G g x
  simp only [GroupActions.Variety.mapPoints_comp] at he
  rw [← he, Equiv.symm_apply_apply]

/-- On a pair of rational sections the action morphism is left multiplication of cosets. -/
theorem flagActionMorphism_pair (h : (GroupActions.reductiveVariety G).points)
    (x : (flagVariety G).points) :
    lift ((GroupActions.reductiveVariety G).pointsEquivOverHom h)
        ((flagVariety G).pointsEquivOverHom x) ≫ flagActionMorphism G =
      (flagVariety G).pointsEquivOverHom
        (flagVarietyPointsEquiv G
          ((GroupActions.reductivePointsMulEquiv G).symm h •
            (flagVarietyPointsEquiv G).symm x)) := by
  let p : (flagActionProduct G).points :=
    (flagActionProduct G).pointsEquivOverHom.symm
      (lift ((GroupActions.reductiveVariety G).pointsEquivOverHom h)
        ((flagVariety G).pointsEquivOverHom x))
  have hp : (flagActionProduct G).pointsEquivOverHom p =
      lift ((GroupActions.reductiveVariety G).pointsEquivOverHom h)
        ((flagVariety G).pointsEquivOverHom x) :=
    (flagActionProduct G).pointsEquivOverHom.apply_symm_apply _
  have hpH : GroupActions.Variety.mapPoints (flagActionFst G) p = h := by
    apply (GroupActions.reductiveVariety G).pointsEquivOverHom.injective
    change (flagActionProduct G).pointsEquivOverHom p ≫ flagActionFst G = _
    rw [hp]
    exact lift_fst _ _
  have hpX : GroupActions.Variety.mapPoints (flagActionSnd G) p = x := by
    apply (flagVariety G).pointsEquivOverHom.injective
    change (flagActionProduct G).pointsEquivOverHom p ≫ flagActionSnd G = _
    rw [hp]
    exact lift_snd _ _
  have he := flagActionMorphism_points G p
  rw [hpH, hpX] at he
  have hh := congrArg (flagVariety G).pointsEquivOverHom he
  change (flagActionProduct G).pointsEquivOverHom p ≫ flagActionMorphism G = _ at hh
  rw [hp] at hh
  exact hh

end
end SchubertGeometry