import OrbitComplexity.Paper.Deodhar.Parameters
import OrbitComplexity.GroupActions.Tori.ImmersedOrbitRank

/-! # Torus orbits in Deodhar parameters

The nonzero coordinates determine a parameter orbit's character span. Full coordinate
support gives the subword weight rank, and every orbit is bounded by that rank.
-/

open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety BruhatIntervals
noncomputable section
namespace SchubertOrbits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusReduced

private def coordinate (x : (deodharParameters G expression).points)
    (j : deodharIndex G expression) : K :=
  affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
    (mapPoints (deodharParameterInclusion G expression) x) j

private def weights (j : deodharIndex G expression) (k : G.torusIndex) : ℝ :=
  ((subwordCharacter G expression j.down).toAdd k : ℝ)

private theorem weight_rank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (weights G expression))) =
      subwordWeightDim (weylRealization G.rootBase) expression := by
  have hr : Set.range (weights G expression) = Set.range
      (fun (j : {position : Fin word.length //
          position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
            negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression})
        (k : G.torusIndex) => ((subwordCharacter G expression j).toAdd k : ℝ)) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.down, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j⟩, rfl⟩
  exact (congrArg (fun S : Set (G.torusIndex → ℝ) =>
    Module.finrank ℝ (Submodule.span ℝ S)) hr).trans (subwordCharacter_rank G expression)

private theorem orbit_rank (x : (deodharParameters G expression).points) :
    letI := deodharParameterAction G expression
    orbitNatDim (torusVariety G) (deodharParameters G expression) x =
      Module.finrank ℝ (Submodule.span ℝ (Set.range
        (fun j : {j // coordinate G expression x j ≠ 0} => weights G expression j.val))) := by
  classical
  let : Fintype (deodharIndex G expression) := Fintype.ofFinite _
  let := deodharParameterAction G expression
  exact torus_orbitNatDim_of_immersion G (deodharParameters G expression)
    (deodharParameterInclusion G expression)
    (fun j => (subwordCharacter G expression j.down).toAdd) x
    (fun t j => deodharParameter_smul G expression t x j)

/-- A parameter point with every coordinate nonzero has the subword's full torus orbit rank. -/
theorem deodharParameter_orbit_rank (x : (deodharParameters G expression).points)
    (hx : ∀ j : deodharIndex G expression,
      affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
        (mapPoints (deodharParameterInclusion G expression) x) j ≠ 0) :
    letI := deodharParameterAction G expression
    orbitNatDim (torusVariety G) (deodharParameters G expression) x =
      subwordWeightDim (weylRealization G.rootBase) expression := by
  let := deodharParameterAction G expression
  have hr : Set.range
      (fun j : {j // coordinate G expression x j ≠ 0} => weights G expression j.val) =
        Set.range (weights G expression) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j, hx j⟩, rfl⟩
  exact (orbit_rank G expression x).trans
    ((congrArg (fun S : Set (G.torusIndex → ℝ) =>
      Module.finrank ℝ (Submodule.span ℝ S)) hr).trans (weight_rank G expression))

/-- Every parameter point has torus orbit dimension at most the subword's weight rank. -/
theorem deodharParameter_orbit_le (x : (deodharParameters G expression).points) :
    letI := deodharParameterAction G expression
    orbitNatDim (torusVariety G) (deodharParameters G expression) x ≤
      subwordWeightDim (weylRealization G.rootBase) expression := by
  let := deodharParameterAction G expression
  have hr : Set.range
      (fun j : {j // coordinate G expression x j ≠ 0} => weights G expression j.val) ⊆
        Set.range (weights G expression) := by
    rintro v ⟨j, rfl⟩
    exact ⟨j.val, rfl⟩
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range (weights G expression))) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range (weights G expression))
  exact (orbit_rank G expression x).le.trans
    ((Submodule.finrank_mono (Submodule.span_mono hr)).trans_eq (weight_rank G expression))

end SchubertOrbits
