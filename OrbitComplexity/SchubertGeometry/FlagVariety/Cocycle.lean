import OrbitComplexity.SchubertGeometry.FlagVariety.TripleCharts

/-!
# The cocycle of flag chart transitions

The changed coordinates on a triple intersection define its cyclic transition morphism.
Rational flag coordinates determine this morphism, proving the cocycle identity needed
for scheme gluing.

## Main definitions

* `SchubertGeometry.flagTripleTransition`: cyclic permutation of the three charts.

## Main results

* `SchubertGeometry.flagTripleTransition_cycle`: three cyclic changes give the identity.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchubertGeometry
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The first projection from a triple overlap is an open immersion. -/
instance flagTripleFst_isOpen (g h k : G.points) :
    IsOpenImmersion (flagTripleFst G g h k).left := by
  change IsOpenImmersion
    (pullback.fst (flagOverlapInclusion G g h).left (flagOverlapInclusion G g k).left)
  infer_instance

/-- A cyclic change of the three charts on their common intersection. -/
def flagTripleTransition (g h k : G.points) :
    (flagTripleVariety G g h k).toOver ⟶ (flagTripleVariety G h k g).toOver := by
  have hc : (flagTripleCoordinate G g h k).left ≫ (flagOverlapInclusion G h k).left =
      (flagTripleFst G g h k ≫ flagTransition G g h).left ≫
        (flagOverlapInclusion G h g).left :=
    by simpa only [Over.comp_left, Category.assoc] using
      congrArg Over.Hom.left (flagTripleCoordinate_comp G g h k)
  let f : (flagTripleVariety G g h k).scheme ⟶ (flagTripleVariety G h k g).scheme :=
    pullback.lift (f := (flagOverlapInclusion G h k).left)
      (g := (flagOverlapInclusion G h g).left) (flagTripleCoordinate G g h k).left
      (flagTripleFst G g h k ≫ flagTransition G g h).left hc
  have hf : f ≫ pullback.fst (flagOverlapInclusion G h k).left
      (flagOverlapInclusion G h g).left = (flagTripleCoordinate G g h k).left :=
    pullback.lift_fst _ _ _
  refine Over.homMk f ?_
  change f ≫ (pullback.fst (flagOverlapInclusion G h k).left
      (flagOverlapInclusion G h g).left ≫ (flagOverlapVariety G h k).toSpec) =
    (flagTripleVariety G g h k).toSpec
  rw [← Category.assoc, hf]
  exact (flagTripleCoordinate G g h k).w

/-- The second projection after a cyclic triple transition is the pairwise transition. -/
theorem flagTripleTransition_snd (g h k : G.points) :
    flagTripleTransition G g h k ≫ flagTripleSnd G h k g =
      flagTripleFst G g h k ≫ flagTransition G g h := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- The first projection after a cyclic triple transition is its lifted coordinate. -/
theorem flagTripleTransition_fst (g h k : G.points) :
    flagTripleTransition G g h k ≫ flagTripleFst G h k g = flagTripleCoordinate G g h k := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- The cyclic triple transition preserves the rational flag of the common chart. -/
theorem flagTripleTransition_flag (g h k : G.points)
    (x : (flagTripleVariety G g h k).points) :
    flagChartPoint G h (GroupActions.Variety.mapPoints (flagOverlapInclusion G h k)
      (GroupActions.Variety.mapPoints (flagTripleFst G h k g)
        (GroupActions.Variety.mapPoints (flagTripleTransition G g h k) x))) =
      flagChartPoint G g (GroupActions.Variety.mapPoints (flagOverlapInclusion G g h)
        (GroupActions.Variety.mapPoints (flagTripleFst G g h k) x)) := by
  have he := congrArg (fun f => GroupActions.Variety.mapPoints f x)
    (flagTripleTransition_fst G g h k)
  simp only [GroupActions.Variety.mapPoints_comp] at he
  rw [he]
  have hc := congrArg (fun f => GroupActions.Variety.mapPoints f x)
    (flagTripleCoordinate_comp G g h k)
  simp only [GroupActions.Variety.mapPoints_comp] at hc
  rw [hc]
  exact flagTransition_flag G g h _

/-- Three cyclic chart changes compose to the identity on the triple intersection. -/
theorem flagTripleTransition_cycle (g h k : G.points) :
    flagTripleTransition G g h k ≫ flagTripleTransition G h k g ≫
      flagTripleTransition G k g h = 𝟙 _ := by
  apply GroupActions.Variety.mapPoints_injective
  funext x
  apply GroupActions.Variety.mapPoints_injective_of_mono (flagTripleFst G g h k)
  apply GroupActions.Variety.mapPoints_injective_of_mono (flagOverlapInclusion G g h)
  apply flagChartPoint_injective G g
  simp only [GroupActions.Variety.mapPoints_comp, GroupActions.Variety.mapPoints_id,
    flagTripleTransition_flag]

end
end SchubertGeometry
