import OrbitComplexity.GroupActions.Rosenlicht.RelationFibreMaps
import OrbitComplexity.GroupActions.Rosenlicht.RelationProjections
import OrbitComplexity.GroupActions.Rosenlicht.AffineRelations
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties

/-!
# RelationPairFibres
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver]
variable [IrreducibleSpace H.scheme] [IrreducibleSpace X.scheme]

/-- A rational point of the relation with prescribed first and second
coordinates puts the second point in the relation fibre over the first. -/
theorem relationFibre_mem_of_pair
    (r : Spec (.of K) ⟶ (orbitRelationVariety H X).scheme) (x y : X.points)
    (hfirst : r ≫ (orbitRelationProjection H X).left = x.val)
    (hsecond : r ≫ (orbitRelationSecond H X).left = y.val) :
    X.pointMap y ∈ Set.range (relationFibreMap H X x) := by
  let z : (orbitRelationVariety H X).scheme := r (IsLocalRing.closedPoint K)
  have hz : (orbitRelationProjection H X).left z = X.pointMap x :=
    congrArg (fun f : Spec (.of K) ⟶ X.scheme ↦ f (IsLocalRing.closedPoint K)) hfirst
  let w := ((orbitRelationProjection H X).left.fiberHomeo (X.pointMap x)).symm ⟨z, hz⟩
  refine ⟨w, ?_⟩
  rw [relationFibreMap_apply]
  dsimp only [w]
  rw [Scheme.Hom.fiberι_fiberHomeo_symm]
  change (orbitRelationSecond H X).left (r (IsLocalRing.closedPoint K)) = X.pointMap y
  exact congrArg (fun f : Spec (.of K) ⟶ X.scheme ↦ f (IsLocalRing.closedPoint K)) hsecond

/-- A relation-chart point puts its second ambient coordinate in the relation
fibre over its first ambient coordinate. -/
theorem relationFibre_mem_of_chartPoint (U V : X.scheme.Opens)
    (p : (X.openSubvariety U).points) (q : (X.openSubvariety V).points)
    (t : Spec (.of K) ⟶ relationChart H X U V)
    (ht : t ≫ relationChartFirst H X U V = p.val)
    (hs : t ≫ relationChartSecond H X U V = q.val) :
    X.pointMap (mapPoints (X.openInclusion V) q) ∈ Set.range
      (relationFibreMap H X (mapPoints (X.openInclusion U) p)) := by
  apply relationFibre_mem_of_pair H X (t ≫ relationChartInclusion H X U V)
  · change (t ≫ relationChartInclusion H X U V) ≫
      (orbitRelationProjection H X).left = p.val ≫ U.ι
    rw [Category.assoc, ← relationChartFirst_fac, ← Category.assoc, ht]
    rfl
  · change (t ≫ relationChartInclusion H X U V) ≫
      (orbitRelationSecond H X).left = q.val ≫ V.ι
    rw [Category.assoc, ← relationChartSecond_fac, ← Category.assoc, hs]
    rfl

end

end GroupActions.Variety
