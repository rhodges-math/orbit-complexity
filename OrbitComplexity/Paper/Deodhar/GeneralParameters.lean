import OrbitComplexity.GroupActions.Varieties.CoordinateOpens
import OrbitComplexity.Paper.Deodhar.ParameterOrbits
import OrbitComplexity.GroupActions.Varieties.IrreduciblePoints

/-! # General Deodhar parameters

Requiring every decreasing-step coordinate to be nonzero gives a nonempty open dense
parameter locus. Its torus orbits have the full subword weight rank.
-/

open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety BruhatIntervals
noncomputable section
namespace SchubertOrbits
universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private def coordinate (x : (deodharParameters G expression).points)
    (j : deodharIndex G expression) : K :=
  affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
    (mapPoints (deodharParameterInclusion G expression) x) j

/-- General parameters have nonzero coordinates at every omitted or decreasing position. -/
def deodharGeneralParameters : Set (deodharParameters G expression).points :=
  {x | ∀ j, coordinate G expression x j ≠ 0}

private theorem general_iff (x : (deodharParameters G expression).points) :
    x ∈ deodharGeneralParameters G expression ↔
      ∀ j : deodharIndex G expression,
        j.down.val ∈ negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression →
          coordinate G expression x j ≠ 0 := by
  constructor
  · intro hx j _
    exact hx j
  · intro hx j
    rcases j.down.property with hj | hj
    · exact (deodharParameter_points G expression).subset ⟨x, rfl⟩ j hj
    · exact hx j hj

private theorem general_open : IsOpen (deodharGeneralParameters G expression) := by
  classical
  let : Fintype (deodharIndex G expression) := Fintype.ofFinite _
  let A := affineSpaceVariety K (deodharIndex G expression)
  let S : Finset (deodharIndex G expression) := Finset.univ
  let U : A.scheme.Opens := PrimeSpectrum.basicOpen
    (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial (deodharIndex G expression) K))
  have h : deodharGeneralParameters G expression =
      (A.pointMap ∘ mapPoints (deodharParameterInclusion G expression)) ⁻¹' (U : Set _) := by
    ext x
    exact ((affineBasicOpen_points S (mapPoints (deodharParameterInclusion G expression) x)).trans
      (by simp only [S, Finset.mem_univ, forall_const]; rfl)).symm
  rw [h]
  exact U.isOpen.preimage
    (A.continuous_pointMap.comp (continuous_mapPoints (deodharParameterInclusion G expression)))

set_option maxHeartbeats 400000 in
private theorem general_nonempty : (deodharGeneralParameters G expression).Nonempty := by
  let a := (affineSpaceVarietyPointsEquiv K (deodharIndex G expression)).symm (fun _ => 1)
  have ha : a ∈ Set.range (mapPoints (deodharParameterInclusion G expression)) := by
    apply (deodharParameter_points G expression).symm.subset
    intro j _
    change affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
      ((affineSpaceVarietyPointsEquiv K (deodharIndex G expression)).symm _) j ≠ 0
    rw [Equiv.apply_symm_apply]
    exact one_ne_zero
  obtain ⟨x, hx⟩ := ha
  refine ⟨x, ?_⟩
  intro j
  change affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
    (mapPoints (deodharParameterInclusion G expression) x) j ≠ 0
  rw [hx]
  change affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
    ((affineSpaceVarietyPointsEquiv K (deodharIndex G expression)).symm _) j ≠ 0
  rw [Equiv.apply_symm_apply]
  exact one_ne_zero

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusReduced

/-- General parameters are the nonzero decreasing-coordinate locus, which is nonempty,
open and dense, and every point in it has the full subword torus orbit rank. -/
theorem deodharGeneral_properties :
    (∀ x : (deodharParameters G expression).points,
      x ∈ deodharGeneralParameters G expression ↔
        ∀ j : deodharIndex G expression,
          j.down.val ∈ negativeSteps
            (ReductiveGroups.weylCoxeterSystem G.rootBase) expression →
          affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
            (mapPoints (deodharParameterInclusion G expression) x) j ≠ 0) ∧
    IsOpen (deodharGeneralParameters G expression) ∧
    Dense (deodharGeneralParameters G expression) ∧
    (deodharGeneralParameters G expression).Nonempty ∧
    (letI := deodharParameterAction G expression
     ∀ x ∈ deodharGeneralParameters G expression,
       orbitNatDim (torusVariety G) (deodharParameters G expression) x =
         subwordWeightDim (weylRealization G.rootBase) expression) := by
  refine ⟨general_iff G expression, general_open G expression,
    (general_open G expression).dense (general_nonempty G expression),
    general_nonempty G expression, ?_⟩
  let := deodharParameterAction G expression
  intro x hx
  exact deodharParameter_orbit_rank G expression x hx

end SchubertOrbits
