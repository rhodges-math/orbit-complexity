import OrbitComplexity.GroupActions.Varieties.MixedCoordinates
import OrbitComplexity.SchubertGeometry.Deodhar.Parameters

/-! # Products of Deodhar parameter coordinates

The omitted coordinates form a split torus and the decreasing coordinates form affine space.
Their product is isomorphic to the open parameter variety, with the expected coordinate counts.
-/

open CategoryTheory AlgebraicGeometry GroupActions CartesianMonoidalCategory MonoidalCategory
open BruhatIntervals
noncomputable section
namespace SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- The omitted positions inside the selected parameter coordinates. -/
def deodharEqualPositions : Finset (deodharIndex G expression) := by
  classical
  letI : Fintype (deodharIndex G expression) := Fintype.ofFinite _
  exact Finset.univ.filter (fun j : deodharIndex G expression =>
    j.down.val ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)

/-- The parameter variety is a split torus in the omitted coordinates times affine space. -/
def deodharParameterProductIso :
    (deodharParameters G expression).toOver ≅
      (reductiveVariety (ReductiveGroups.SplitTorus.groupData K
        (deodharEqualPositions G expression))).toOver ⊗
          (affineSpaceVariety K {j : deodharIndex G expression //
            j ∉ deodharEqualPositions G expression}).toOver := by
  classical
  change ((affineSpaceVariety K (deodharIndex G expression)).openSubvariety
    (PrimeSpectrum.basicOpen (∏ j ∈ deodharEqualPositions G expression,
      (MvPolynomial.X j : MvPolynomial (deodharIndex G expression) K)))).toOver ≅ _
  exact mixedCoordinateIso K (deodharEqualPositions G expression)

private def omittedIndexEquiv :
    (deodharEqualPositions G expression) ≃ ULift.{u}
      {j : Fin word.length // j ∈ equalSteps
        (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} := by
  classical
  refine {
    toFun := fun j => ⟨⟨j.val.down.val, ?_⟩⟩
    invFun := fun j => ⟨⟨⟨j.down.val, Or.inl j.down.property⟩⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa only [deodharEqualPositions, Finset.mem_filter, Finset.mem_univ, true_and]
      using j.property
  · simp only [deodharEqualPositions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact j.down.property
  · intro j
    rfl
  · intro j
    rfl

private def decreasingIndexEquiv :
    {j : deodharIndex G expression // j ∉ deodharEqualPositions G expression} ≃ ULift.{u}
      {j : Fin word.length // j ∈ negativeSteps
        (ReductiveGroups.weylCoxeterSystem G.rootBase) expression} := by
  classical
  refine {
    toFun := fun j => ⟨⟨j.val.down.val, ?_⟩⟩
    invFun := fun j => ⟨⟨⟨j.down.val, Or.inr j.down.property⟩⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h := j.val.down.property
    have he : j.val.down.val ∉ equalSteps
        (ReductiveGroups.weylCoxeterSystem G.rootBase) expression := by
      simpa only [deodharEqualPositions, Finset.mem_filter, Finset.mem_univ, true_and]
        using j.property
    exact h.resolve_left he
  · simp only [deodharEqualPositions, Finset.mem_filter, Finset.mem_univ, true_and]
    intro he
    exact j.down.property.2 he.symm
  · intro j
    rfl
  · intro j
    rfl

/-- The torus and affine coordinate counts are the omitted and decreasing step counts. -/
theorem deodharParameterProduct_counts :
    Nat.card (deodharEqualPositions G expression) =
      (equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression).ncard ∧
    Nat.card {j : deodharIndex G expression // j ∉ deodharEqualPositions G expression} =
      (negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression).ncard := by
  constructor
  · rw [Nat.card_congr (omittedIndexEquiv G expression), Nat.card_ulift, Nat.card_coe_set_eq]
  · rw [Nat.card_congr (decreasingIndexEquiv G expression), Nat.card_ulift, Nat.card_coe_set_eq]

end SchubertGeometry
