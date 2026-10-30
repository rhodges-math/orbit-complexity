import OrbitComplexity.SchubertGeometry.Deodhar.Parameters
import OrbitComplexity.BruhatIntervals.Words.Prefix
import OrbitComplexity.GroupActions.Varieties.OpenPointLifts
import OrbitComplexity.GroupActions.Varieties.AffineMorphisms

/-! # Projection to prefix parameters

Restricting the selected coordinates to an initial word preserves the nonzero omitted
coordinates and therefore defines a morphism between the parameter opens.
-/

open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety BruhatIntervals
noncomputable section
namespace SchubertGeometry
universe u
private theorem affineRename_coord {K : Type u} [Field K]
    {ι κ : Type u} [Finite ι] [Finite κ] (f : κ → ι)
    (x : (affineSpaceVariety K ι).points) (j : κ) :
    affineSpaceVarietyPointsEquiv K κ (mapPoints (affineMorphism (MvPolynomial.rename f)) x) j =
      affineSpaceVarietyPointsEquiv K ι x (f j) := by
  obtain ⟨p, rfl⟩ := (affineVarietyPointsEquiv K (MvPolynomial ι K)).symm.surjective x
  change (affineVarietyPointsEquiv K (MvPolynomial κ K)
    (mapPoints (affineMorphism (MvPolynomial.rename f))
      ((affineVarietyPointsEquiv K (MvPolynomial ι K)).symm p))) (MvPolynomial.X j) =
    ((affineVarietyPointsEquiv K (MvPolynomial ι K))
      ((affineVarietyPointsEquiv K (MvPolynomial ι K)).symm p)) (MvPolynomial.X (f j))
  rw [affineMorphism_points (MvPolynomial.rename f) p, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact congrArg p (MvPolynomial.rename_X f j)

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- A selected prefix position determines the same selected position in the full word. -/
def deodharTakeIndex (n : ℕ) (j : deodharIndex G (expression.take n)) :
    deodharIndex G expression := by
  refine ⟨⟨Subexpression.takePosition n j.down.val, ?_⟩⟩
  rcases j.down.property with he | hn
  · exact Or.inl ((expression.equalSteps_take
      (ReductiveGroups.weylCoxeterSystem G.rootBase) n j.down.val).mp he)
  · exact Or.inr ((expression.negativeSteps_take
      (ReductiveGroups.weylCoxeterSystem G.rootBase) n j.down.val).mp hn)

private def affineProjection (n : ℕ) :
    (affineSpaceVariety K (deodharIndex G expression)).toOver ⟶
      (affineSpaceVariety K (deodharIndex G (expression.take n))).toOver :=
  affineMorphism (MvPolynomial.rename (deodharTakeIndex G expression n))

private theorem affineProjection_coord (n : ℕ)
    (x : (affineSpaceVariety K (deodharIndex G expression)).points)
    (j : deodharIndex G (expression.take n)) :
    affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n))
      (mapPoints (affineProjection G expression n) x) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G expression) x
        (deodharTakeIndex G expression n j) := by
  exact affineRename_coord (deodharTakeIndex G expression n) x j

private theorem projection_range (n : ℕ) (x : (deodharParameters G expression).points) :
    mapPoints (deodharParameterInclusion G expression ≫ affineProjection G expression n) x ∈
      Set.range (mapPoints (deodharParameterInclusion G (expression.take n))) := by
  have hx := (deodharParameter_points G expression).subset ⟨x, rfl⟩
  have hp : ∀ j : deodharIndex G (expression.take n),
      j.down.val ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) (expression.take n) →
        affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n))
          (mapPoints (deodharParameterInclusion G expression ≫ affineProjection G expression n) x)
          j ≠ 0 := by
    intro j hj
    have hj' := (expression.equalSteps_take
      (ReductiveGroups.weylCoxeterSystem G.rootBase) n j.down.val).mp hj
    have hn := hx (deodharTakeIndex G expression n j) hj'
    have hc := affineProjection_coord G expression n
      (mapPoints (deodharParameterInclusion G expression) x) j
    have he := congrArg (fun y => affineSpaceVarietyPointsEquiv K
      (deodharIndex G (expression.take n)) y j)
        (mapPoints_comp (deodharParameterInclusion G expression)
          (affineProjection G expression n) x)
    exact fun h => hn ((he.trans hc).symm.trans h)
  exact (deodharParameter_points G (expression.take n)).symm.subset hp

/-- Forgetting coordinates after the first letters gives the prefix parameter morphism. -/
def deodharParameterProjection (n : ℕ) :
    (deodharParameters G expression).toOver ⟶
      (deodharParameters G (expression.take n)).toOver :=
  liftOpen (deodharParameterInclusion G expression ≫ affineProjection G expression n)
    (deodharParameterInclusion G (expression.take n)) (projection_range G expression n)

private theorem deodharParameterProjection_comp (n : ℕ) :
    deodharParameterProjection G expression n ≫
        deodharParameterInclusion G (expression.take n) =
      deodharParameterInclusion G expression ≫ affineProjection G expression n :=
  liftOpen_comp _ _ (projection_range G expression n)

/-- Prefix parameter projection retains the coordinates at the same word positions. -/
theorem deodharParameterProjection_coord (n : ℕ)
    (x : (deodharParameters G expression).points)
    (j : deodharIndex G (expression.take n)) :
    affineSpaceVarietyPointsEquiv K (deodharIndex G (expression.take n))
      (mapPoints (deodharParameterInclusion G (expression.take n))
        (mapPoints (deodharParameterProjection G expression n) x)) j =
      affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
        (mapPoints (deodharParameterInclusion G expression) x)
        (deodharTakeIndex G expression n j) := by
  have he := (mapPoints_comp (deodharParameterProjection G expression n)
    (deodharParameterInclusion G (expression.take n)) x).symm
  have hf := congrArg (fun f => mapPoints f x) (deodharParameterProjection_comp G expression n)
  have hg := mapPoints_comp (deodharParameterInclusion G expression)
    (affineProjection G expression n) x
  have hh := congrArg (fun y => affineSpaceVarietyPointsEquiv K
    (deodharIndex G (expression.take n)) y j) (he.trans (hf.trans hg))
  exact hh.trans (affineProjection_coord G expression n
    (mapPoints (deodharParameterInclusion G expression) x) j)

end SchubertGeometry
