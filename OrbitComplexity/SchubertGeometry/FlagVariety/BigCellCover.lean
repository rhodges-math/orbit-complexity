import OrbitComplexity.SchubertGeometry.FlagVariety.BigCellPoints
import OrbitComplexity.GroupActions.Actions.Translations
import OrbitComplexity.GroupActions.Varieties.OpenPointLifts
import Mathlib.AlgebraicGeometry.Gluing

/-!
# A cover of the reductive group by translated big cells

Left translates of the big cell cover the reductive group. Each rational group point lies
in its own translate, and rational detection of open containment proves that these
translates cover the whole scheme.

## Main definitions

* `SchubertGeometry.translatedBigCell`: a translated big-cell open immersion.
* `SchubertGeometry.bigCellCover`: the corresponding open cover of the group scheme.

## Main results

* `SchubertGeometry.translatedBigCell_points`: multiplication on rational coordinates.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- Left translation of the big-cell open immersion by a rational group point. -/
def translatedBigCell (g : G.points) :
    (bigCellVariety G).toOver ⟶ (GroupActions.reductiveVariety G).toOver :=
  bigCellMorphism G ≫
    (GroupActions.leftTranslation (GroupActions.reductiveVariety G)
      (GroupActions.reductivePointsMulEquiv G g)).hom

/-- A translated big cell is an open subvariety of the reductive group. -/
instance translatedBigCell_isOpen (g : G.points) :
    IsOpenImmersion (translatedBigCell G g).left := by
  change IsOpenImmersion ((bigCellMorphism G).left ≫
    (GroupActions.leftTranslation (GroupActions.reductiveVariety G)
      (GroupActions.reductivePointsMulEquiv G g)).hom.left)
  infer_instance

/-- Rational points of a translated big cell are products of its three group coordinates. -/
theorem translatedBigCell_points (g : G.points) (x : (bigCellVariety G).points) :
    GroupActions.Variety.mapPoints (translatedBigCell G g) x =
      GroupActions.reductivePointsEquiv G
        (g * ((GroupActions.oppositeUnipotentPointsMulEquiv G (bigCellPointsEquiv G x).1 :
          G.points) * (GroupActions.borelPointsMulEquiv G (bigCellPointsEquiv G x).2 :
            G.points))) := by
  rw [translatedBigCell, GroupActions.Variety.mapPoints_comp,
    GroupActions.leftTranslation_points, bigCellMorphism_points]
  exact ((GroupActions.reductivePointsMulEquiv G).map_mul _ _).symm

private theorem translatedBigCell_range (g : G.points) :
    GroupActions.reductivePointsEquiv G g ∈
      Set.range (GroupActions.Variety.mapPoints (translatedBigCell G g)) := by
  refine ⟨(bigCellPointsEquiv G).symm (1, 1), ?_⟩
  rw [translatedBigCell_points, Equiv.apply_symm_apply]
  simp only [map_one, OneMemClass.coe_one, mul_one]

private theorem translatedBigCell_cover (x : (GroupActions.reductiveVariety G).scheme) :
    ∃ (g : G.points) (y : (bigCellVariety G).scheme), (translatedBigCell G g).left y = x := by
  let U : (GroupActions.reductiveVariety G).scheme.Opens :=
    ⨆ g : G.points, (translatedBigCell G g).left.opensRange
  have hU := GroupActions.Variety.range_subset_open_of_points
    (𝟙 (GroupActions.reductiveVariety G).toOver) U (fun p => by
      rw [GroupActions.Variety.mapPoints_id]
      obtain ⟨g, rfl⟩ := (GroupActions.reductivePointsEquiv G).surjective p
      apply Opens.mem_iSup.mpr
      obtain ⟨q, hq⟩ := translatedBigCell_range G g
      refine ⟨g, (bigCellVariety G).pointMap q, ?_⟩
      rw [← GroupActions.Variety.pointMap_mapPoints, hq])
  have hx : x ∈ U := hU ⟨x, rfl⟩
  obtain ⟨g, hg⟩ := Opens.mem_iSup.mp hx
  obtain ⟨y, hy⟩ := hg
  exact ⟨g, y, hy⟩

/-- Translates of the big cell form an open cover of the reductive group scheme. -/
def bigCellCover : Scheme.OpenCover.{u} (GroupActions.reductiveVariety G).scheme where
  I₀ := G.points
  X _ := (bigCellVariety G).scheme
  f g := (translatedBigCell G g).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨translatedBigCell_cover G, inferInstance⟩

end
end SchubertGeometry
