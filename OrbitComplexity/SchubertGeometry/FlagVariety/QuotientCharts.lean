import OrbitComplexity.SchubertGeometry.FlagVariety.GluedPoints
import OrbitComplexity.SchubertGeometry.FlagVariety.BigCellCover
import OrbitComplexity.GroupActions.Varieties.Noetherian

/-! # Local quotient morphisms

Translated big cells give compatible unipotent coordinates for the flag scheme.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem bigCellReduced : IsReduced (bigCellVariety G).toOver.left :=
  (bigCellVariety G).reduced

private theorem bigCellNoetherian : IsNoetherian (bigCellVariety G).toOver.left :=
  GroupActions.Variety.noetherian (bigCellVariety G)

attribute [local instance] bigCellReduced bigCellNoetherian

/-- The intersection of two translated big-cell charts of the reductive group. -/
abbrev bigCellOverlapVariety (g h : G.points) : GroupActions.Variety K where
  scheme := pullback (translatedBigCell G g).left (translatedBigCell G h).left
  toSpec := pullback.fst (translatedBigCell G g).left (translatedBigCell G h).left ≫
    (bigCellVariety G).toSpec
  reduced := isReduced_of_isOpenImmersion
    (pullback.fst (translatedBigCell G g).left (translatedBigCell G h).left)

/-- The first projection of an intersection of translated big cells. -/
def bigCellOverlapFst (g h : G.points) :
    (bigCellOverlapVariety G g h).toOver ⟶ (bigCellVariety G).toOver :=
  Over.homMk (pullback.fst (translatedBigCell G g).left (translatedBigCell G h).left) rfl

/-- The second projection of an intersection of translated big cells. -/
def bigCellOverlapSnd (g h : G.points) :
    (bigCellOverlapVariety G g h).toOver ⟶ (bigCellVariety G).toOver :=
  Over.homMk (pullback.snd (translatedBigCell G g).left (translatedBigCell G h).left) (by
    have hi : (translatedBigCell G g).left ≫ (GroupActions.reductiveVariety G).toSpec =
        (bigCellVariety G).toSpec := (translatedBigCell G g).w
    have hj : (translatedBigCell G h).left ≫ (GroupActions.reductiveVariety G).toSpec =
        (bigCellVariety G).toSpec := (translatedBigCell G h).w
    change pullback.snd (translatedBigCell G g).left (translatedBigCell G h).left ≫
        (bigCellVariety G).toSpec =
      pullback.fst (translatedBigCell G g).left (translatedBigCell G h).left ≫
        (bigCellVariety G).toSpec
    conv_lhs => rw [← hj]
    conv_rhs => rw [← hi]
    rw [← Category.assoc, ← Category.assoc, pullback.condition])

/-- The translated images of the two overlap projections agree. -/
theorem bigCellOverlap_condition (g h : G.points) :
    bigCellOverlapFst G g h ≫ translatedBigCell G g =
      bigCellOverlapSnd G g h ≫ translatedBigCell G h := by
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- The local quotient morphism on a translated big cell forgets its Borel coordinate. -/
def bigCellFlagChart (g : G.points) : (bigCellVariety G).scheme ⟶ flagScheme G :=
  (bigCellFst G).left ≫ flagSchemeChart G g

/-- Local quotient morphisms commute with the structure maps to the base field. -/
theorem bigCellFlagChart_toSpec (g : G.points) :
    bigCellFlagChart G g ≫ flagSchemeToSpec G = (bigCellVariety G).toSpec := by
  rw [bigCellFlagChart, Category.assoc, flagSchemeChart_toSpec]
  exact (bigCellFst G).w

/-- On rational points a local quotient morphism keeps the unipotent chart coordinate. -/
theorem bigCellFlagChart_points (g : G.points) (x : (bigCellVariety G).points) :
    x.val ≫ bigCellFlagChart G g =
      (flagSchemeChartPoints G g (bigCellPointsEquiv G x).1).val := by
  rw [bigCellPointsEquiv_fst]
  exact (Category.assoc _ _ _).symm

omit [IsAlgClosed K] [CharZero K] in
private theorem flagProjection_borel (a : G.points) (b : G.borelPoints) :
    flagProjection G (a * b) = flagProjection G a := by
  rw [flagProjection_eq_iff]
  have he : (a * b)⁻¹ * a = (b : G.points)⁻¹ := by group
  rw [he]
  exact G.borelPoints.inv_mem b.property

/-- Local unipotent quotient coordinates agree as rational flags on an overlap. -/
theorem bigCellOverlap_flags (g h : G.points)
    (x : (bigCellOverlapVariety G g h).points) :
    flagChartPoint G g (bigCellPointsEquiv G
      (GroupActions.Variety.mapPoints (bigCellOverlapFst G g h) x)).1 =
      flagChartPoint G h (bigCellPointsEquiv G
        (GroupActions.Variety.mapPoints (bigCellOverlapSnd G g h) x)).1 := by
  have he := congrArg (fun f => GroupActions.Variety.mapPoints f x)
    (bigCellOverlap_condition G g h)
  simp only [GroupActions.Variety.mapPoints_comp, translatedBigCell_points] at he
  have hgroup := (GroupActions.reductivePointsEquiv G).injective he
  have hflag := congrArg (flagProjection G) hgroup
  simpa only [flagChartPoint, ← mul_assoc, flagProjection_borel] using hflag

end
end SchubertGeometry
