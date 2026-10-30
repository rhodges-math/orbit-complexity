import OrbitComplexity.SchubertGeometry.FlagVariety.ActionPointCharts

/-! # Compatibility of local flag actions

The local action formulas agree on every intersection of pulled-back flag charts.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem actionChartReduced (g : G.points) :
    IsReduced (flagActionChartVariety G g).toOver.left := (flagActionChartVariety G g).reduced

private theorem actionChartNoetherian (g : G.points) :
    IsNoetherian (flagActionChartVariety G g).toOver.left :=
  GroupActions.Variety.noetherian (flagActionChartVariety G g)

private theorem actionChartSeparated (g : G.points) :
    IsSeparated (flagActionChartVariety G g).toSpec := (flagActionChartVariety G g).separated

private theorem actionChartFiniteType (g : G.points) :
    LocallyOfFiniteType (flagActionChartVariety G g).toSpec :=
  (flagActionChartVariety G g).locallyOfFiniteType

private theorem actionChartQuasiCompact (g : G.points) :
    QuasiCompact (flagActionChartVariety G g).toSpec := (flagActionChartVariety G g).quasiCompact

attribute [local instance] actionChartReduced actionChartNoetherian actionChartSeparated
  actionChartFiniteType actionChartQuasiCompact

private abbrev actionOverlapVariety (g h : G.points) : GroupActions.Variety K where
  scheme := pullback (flagActionChartFst G g).left (flagActionChartFst G h).left
  toSpec := pullback.fst (flagActionChartFst G g).left (flagActionChartFst G h).left ≫
    (flagActionChartVariety G g).toSpec
  reduced := isReduced_of_isOpenImmersion
    (pullback.fst (flagActionChartFst G g).left (flagActionChartFst G h).left)

private def actionOverlapFst (g h : G.points) :
    (actionOverlapVariety G g h).toOver ⟶ (flagActionChartVariety G g).toOver :=
  Over.homMk (pullback.fst (flagActionChartFst G g).left (flagActionChartFst G h).left) rfl

private def actionOverlapSnd (g h : G.points) :
    (actionOverlapVariety G g h).toOver ⟶ (flagActionChartVariety G h).toOver :=
  Over.homMk (pullback.snd (flagActionChartFst G g).left (flagActionChartFst G h).left) (by
    have hi : (flagActionChartFst G g).left ≫ (flagActionProduct G).toSpec =
        (flagActionChartVariety G g).toSpec := (flagActionChartFst G g).w
    have hj : (flagActionChartFst G h).left ≫ (flagActionProduct G).toSpec =
        (flagActionChartVariety G h).toSpec := (flagActionChartFst G h).w
    change pullback.snd (flagActionChartFst G g).left (flagActionChartFst G h).left ≫
        (flagActionChartVariety G h).toSpec =
      pullback.fst (flagActionChartFst G g).left (flagActionChartFst G h).left ≫
        (flagActionChartVariety G g).toSpec
    conv_lhs => rw [← hj]
    conv_rhs => rw [← hi]
    rw [← Category.assoc, ← Category.assoc, pullback.condition])

private theorem actionOverlap_condition (g h : G.points) :
    actionOverlapFst G g h ≫ flagActionChartFst G g =
      actionOverlapSnd G g h ≫ flagActionChartFst G h := by
  apply Over.OverMorphism.ext
  exact pullback.condition

private theorem actionCompatible (g h : G.points) :
    actionOverlapFst G g h ≫ flagActionChartMorphism G g =
      actionOverlapSnd G g h ≫ flagActionChartMorphism G h := by
  apply GroupActions.Variety.mapPoints_injective
  funext p
  simp only [GroupActions.Variety.mapPoints_comp, flagActionChartMorphism_points]
  apply congrArg (flagVarietyPointsEquiv G)
  apply congrArg₂ (fun a x => a • x)
  · have he := congrArg (fun f => GroupActions.Variety.mapPoints (f ≫ flagActionFst G) p)
      (actionOverlap_condition G g h)
    simp only [GroupActions.Variety.mapPoints_comp] at he
    exact congrArg (GroupActions.reductivePointsMulEquiv G).symm he
  · apply (flagVarietyPointsEquiv G).injective
    have he := congrArg (fun f => GroupActions.Variety.mapPoints (f ≫ flagActionSnd G) p)
      (actionOverlap_condition G g h)
    simp only [GroupActions.Variety.mapPoints_comp] at he
    exact (flagActionChart_flag G g
      (GroupActions.Variety.mapPoints (actionOverlapFst G g h) p)).trans
        (he.trans (flagActionChart_flag G h
          (GroupActions.Variety.mapPoints (actionOverlapSnd G g h) p)).symm)

/-- The local action morphisms agree on intersections of the pulled-back flag charts. -/
theorem flagActionChart_compatible (g h : G.points) :
    pullback.fst (flagActionChartFst G g).left (flagActionChartFst G h).left ≫
        (flagActionChartMorphism G g).left =
      pullback.snd (flagActionChartFst G g).left (flagActionChartFst G h).left ≫
        (flagActionChartMorphism G h).left :=
  congrArg Over.Hom.left (actionCompatible G g h)

end
end SchubertGeometry