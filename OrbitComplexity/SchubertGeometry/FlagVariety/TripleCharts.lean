import OrbitComplexity.SchubertGeometry.FlagVariety.Transitions

/-!
# Triple intersections of flag charts

Triple intersections are the pullbacks of the two open overlap inclusions.
The pairwise coordinate change factors through the next required overlap, giving the
coordinate morphism used to cyclically permute the three charts.

## Main definitions

* `SchubertGeometry.flagTripleVariety`: the pullback intersection of two overlaps.
* `SchubertGeometry.flagTripleCoordinate`: the changed coordinate on that intersection.

## Main results

* `SchubertGeometry.flagTripleCoordinate_comp`: its factorization through the next chart.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

private theorem overlapReduced (g h : G.points) :
    IsReduced (flagOverlapVariety G g h).toOver.left :=
  inferInstanceAs (IsReduced (flagOverlapVariety G g h).scheme)

private theorem overlapNoetherian (g h : G.points) :
    IsNoetherian (flagOverlapVariety G g h).toOver.left :=
  inferInstanceAs (IsNoetherian (flagOverlapVariety G g h).scheme)

attribute [local instance] overlapReduced overlapNoetherian

/-- The scheme intersection of two overlaps in the same unipotent chart. -/
abbrev flagTripleVariety (g h k : G.points) : GroupActions.Variety K where
  scheme := pullback (flagOverlapInclusion G g h).left (flagOverlapInclusion G g k).left
  toSpec := pullback.fst (flagOverlapInclusion G g h).left (flagOverlapInclusion G g k).left ≫
    (flagOverlapVariety G g h).toSpec
  reduced := isReduced_of_isOpenImmersion
    (pullback.fst (flagOverlapInclusion G g h).left (flagOverlapInclusion G g k).left)

/-- The first overlap projection of a triple chart intersection. -/
def flagTripleFst (g h k : G.points) :
    (flagTripleVariety G g h k).toOver ⟶ (flagOverlapVariety G g h).toOver :=
  Over.homMk
    (pullback.fst (flagOverlapInclusion G g h).left (flagOverlapInclusion G g k).left) rfl

/-- The second overlap projection of a triple chart intersection. -/
def flagTripleSnd (g h k : G.points) :
    (flagTripleVariety G g h k).toOver ⟶ (flagOverlapVariety G g k).toOver :=
  Over.homMk
    (pullback.snd (flagOverlapInclusion G g h).left (flagOverlapInclusion G g k).left) (by
    change pullback.snd (flagOverlapInclusion G g h).left (flagOverlapInclusion G g k).left ≫
        (flagOverlapVariety G g k).toSpec =
      pullback.fst (flagOverlapInclusion G g h).left (flagOverlapInclusion G g k).left ≫
        (flagOverlapVariety G g h).toSpec
    have hi : (flagOverlapInclusion G g h).left ≫
        (GroupActions.oppositeUnipotentVariety G).toSpec = (flagOverlapVariety G g h).toSpec :=
      (flagOverlapInclusion G g h).w
    have hj : (flagOverlapInclusion G g k).left ≫
        (GroupActions.oppositeUnipotentVariety G).toSpec = (flagOverlapVariety G g k).toSpec :=
      (flagOverlapInclusion G g k).w
    rw [← hi, ← hj, ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The triple intersection projections have the same coordinate in their common chart. -/
theorem flagTriple_condition (g h k : G.points) :
    flagTripleFst G g h k ≫ flagOverlapInclusion G g h =
      flagTripleSnd G g h k ≫ flagOverlapInclusion G g k := by
  apply Over.OverMorphism.ext
  exact pullback.condition (f := (flagOverlapInclusion G g h).left)
    (g := (flagOverlapInclusion G g k).left)

private theorem tripleCoordinate_image (g h k : G.points)
    (x : (flagTripleVariety G g h k).points) :
    GroupActions.Variety.mapPoints
        (flagTripleFst G g h k ≫ flagTransition G g h ≫ flagOverlapInclusion G h g) x ∈
      Set.range (GroupActions.Variety.mapPoints (flagOverlapInclusion G h k)) := by
  rw [GroupActions.Variety.range_mapPoints]
  change _ ∈ Set.range
    (((GroupActions.oppositeUnipotentVariety G).openInclusion (flagOverlap G h k)).left)
  rw [GroupActions.Variety.openInclusion_range]
  apply mem_flagOverlap_of_flag G h k _
    (GroupActions.Variety.mapPoints (flagOverlapCoordinate G g k)
      (GroupActions.Variety.mapPoints (flagTripleSnd G g h k) x))
  simp only [GroupActions.Variety.mapPoints_comp]
  rw [flagTransition_flag, ← flagOverlapCoordinate_flag]
  congr 1
  have he := congrArg (fun f => GroupActions.Variety.mapPoints f x)
    (flagTriple_condition G g h k)
  simpa only [GroupActions.Variety.mapPoints_comp] using he

/-- The changed coordinate on a triple intersection lies in the other required overlap. -/
def flagTripleCoordinate (g h k : G.points) :
    (flagTripleVariety G g h k).toOver ⟶ (flagOverlapVariety G h k).toOver :=
  GroupActions.Variety.liftOpen
    (flagTripleFst G g h k ≫ flagTransition G g h ≫ flagOverlapInclusion G h g)
    (flagOverlapInclusion G h k) (tripleCoordinate_image G g h k)

/-- The lifted triple coordinate agrees with transition through the first overlap. -/
theorem flagTripleCoordinate_comp (g h k : G.points) :
    flagTripleCoordinate G g h k ≫ flagOverlapInclusion G h k =
      flagTripleFst G g h k ≫ flagTransition G g h ≫ flagOverlapInclusion G h g :=
  GroupActions.Variety.liftOpen_comp _ _ _


end
end SchubertGeometry
