import OrbitComplexity.SchubertGeometry.Deodhar.StepIndices
import OrbitComplexity.GroupActions.Varieties.CoordinateSteps

/-! # Successive prefix parameter varieties

An increasing step keeps the same coordinates. A decreasing step adds an additive coordinate,
and an omitted step adds a nonzero additive coordinate.
-/

open CategoryTheory AlgebraicGeometry GroupActions BruhatIntervals
open CartesianMonoidalCategory MonoidalCategory
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- An increasing step leaves the prefix parameter variety unchanged. -/
def deodharPositiveStepIso (n : Fin word.length)
    (hn : n ∈ positiveSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharParameters G (expression.take n.val)).toOver := by
  exact coordinateReindexIso K (deodharStepIndexPositive G expression n hn)
    (deodharEqualPositions G (expression.take (n.val + 1)))
    (deodharEqualPositions G (expression.take n.val))
    (deodharEqualPositions_positive G expression n hn)

/-- A decreasing step adds one unrestricted additive parameter. -/
def deodharNegativeStepIso (n : Fin word.length)
    (hn : n ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharParameters G (expression.take n.val)).toOver ⊗ (additiveVariety K).toOver := by
  classical
  let e := deodharStepIndexSelected G expression n (Or.inr hn)
  let S := deodharEqualPositions G (expression.take n.val)
  let T : Finset (deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1}) :=
    coordinateStepInl S
  have hne : n ∉ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression :=
    fun he => hn.2 he.symm
  have h : (deodharEqualPositions G (expression.take (n.val + 1))).map e.toEmbedding = T := by
    exact (deodharEqualPositions_selected G expression n (Or.inr hn)).trans (by
      rw [ite_eq_right hne]
      rfl)
  let r : ((affineSpaceVariety K
      (deodharIndex G (expression.take (n.val + 1)))).openSubvariety
        (coordinateOpen K (deodharEqualPositions G (expression.take (n.val + 1))))).toOver ≅
      ((affineSpaceVariety K (deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1})).openSubvariety
        (coordinateOpen K T)).toOver :=
    coordinateReindexIso K e (deodharEqualPositions G (expression.take (n.val + 1))) T h
  let c : ((affineSpaceVariety K
      (deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1})).openSubvariety
        (coordinateOpen K T)).toOver ≅
      (deodharParameters G (expression.take n.val)).toOver ⊗ (additiveVariety K).toOver :=
    coordinateStepIso K S
  exact r ≪≫ c

/-- An omitted step adds one nonzero additive parameter. -/
def deodharEqualStepIso (n : Fin word.length)
    (hn : n ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression) :
    (deodharParameters G (expression.take (n.val + 1))).toOver ≅
      (deodharParameters G (expression.take n.val)).toOver ⊗
        ((additiveVariety K).openSubvariety
          (PrimeSpectrum.basicOpen (SymmetricAlgebra.ι K K 1))).toOver := by
  classical
  let e := deodharStepIndexSelected G expression n (Or.inl hn)
  let S := deodharEqualPositions G (expression.take n.val)
  let T : Finset (deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1}) :=
    coordinateStepUnit S
  have h : (deodharEqualPositions G (expression.take (n.val + 1))).map e.toEmbedding = T := by
    exact (deodharEqualPositions_selected G expression n (Or.inl hn)).trans (by
      rw [ite_eq_left hn]
      ext j
      simp only [T, coordinateStepUnit, coordinateStepInl, Finset.mem_insert, Finset.mem_map]
      rfl)
  let r : ((affineSpaceVariety K
      (deodharIndex G (expression.take (n.val + 1)))).openSubvariety
        (coordinateOpen K (deodharEqualPositions G (expression.take (n.val + 1))))).toOver ≅
      ((affineSpaceVariety K (deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1})).openSubvariety
        (coordinateOpen K T)).toOver :=
    coordinateReindexIso K e (deodharEqualPositions G (expression.take (n.val + 1))) T h
  let c : ((affineSpaceVariety K
      (deodharIndex G (expression.take n.val) ⊕ PUnit.{u+1})).openSubvariety
        (coordinateOpen K T)).toOver ≅
      (deodharParameters G (expression.take n.val)).toOver ⊗
        ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver :=
    coordinateUnitStepIso K S
  exact r ≪≫ c


end SchubertGeometry
