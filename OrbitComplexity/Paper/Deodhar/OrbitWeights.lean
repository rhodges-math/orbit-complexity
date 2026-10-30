import OrbitComplexity.Paper.Deodhar.GeneralParameters

/-! # Root-weight spans of parameter orbits

Nonzero selected coordinates carry negative signed-root characters. Their real root span
is contained in the subexpression weight span and equals it at general parameters.
The torus orbit dimension is the rank of this active span.
-/

open CategoryTheory AlgebraicGeometry GroupActions ReductiveGroups BruhatIntervals
open SchubertGeometry
namespace SchubertOrbits
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private def parameterCoordinate (x : (deodharParameters G expression).points)
    (j : deodharIndex G expression) : K :=
  affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
    (Variety.mapPoints (deodharParameterInclusion G expression) x) j

/-- The real span of negative signed roots with nonzero selected parameter coordinates. -/
def deodharOrbitWeightSpan (x : (deodharParameters G expression).points) :
    Submodule ℝ (G.rootBase.support →₀ ℝ) :=
  Submodule.span ℝ (Set.range
    (fun j : {j : deodharIndex G expression // parameterCoordinate G expression x j ≠ 0} =>
      -subwordRoot (weylRealization G.rootBase) expression j.val.down.val))

/-- Active root weights of a parameter point lie in the subexpression weight span. -/
theorem deodharOrbitWeightSpan_le (x : (deodharParameters G expression).points) :
    deodharOrbitWeightSpan G expression x ≤
      subwordWeightSpan (weylRealization G.rootBase) expression := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact Submodule.neg_mem _ (Submodule.subset_span ⟨j.val.down.val, j.val.down.property, rfl⟩)

private theorem deodharOrbitWeightSpan_eq (x : (deodharParameters G expression).points)
    (hx : ∀ j : deodharIndex G expression, parameterCoordinate G expression x j ≠ 0) :
    deodharOrbitWeightSpan G expression x =
      subwordWeightSpan (weylRealization G.rootBase) expression := by
  apply le_antisymm (deodharOrbitWeightSpan_le G expression x)
  rw [subwordWeightSpan_eq_neg]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  exact Submodule.subset_span ⟨⟨⟨⟨j, hj⟩⟩, hx ⟨⟨j, hj⟩⟩⟩, rfl⟩

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusReduced

/-- A parameter torus orbit has the dimension of its active negative-root span. -/
theorem deodharParameter_orbit_weightSpan (x : (deodharParameters G expression).points) :
    letI := deodharParameterAction G expression
    orbitNatDim (torusVariety G) (deodharParameters G expression) x =
      Module.finrank ℝ (deodharOrbitWeightSpan G expression x) := by
  classical
  let : Fintype (deodharIndex G expression) := Fintype.ofFinite _
  let := deodharParameterAction G expression
  have hr := torus_orbitNatDim_of_immersion G (deodharParameters G expression)
    (deodharParameterInclusion G expression)
    (fun j => (subwordCharacter G expression j.down).toAdd) x
    (fun t j => deodharParameter_smul G expression t x j)
  let A := {j : deodharIndex G expression // parameterCoordinate G expression x j ≠ 0}
  have hn (j : A) : normalizedRoot G.rootBase
      (G.rootSystem.reflectionPerm (subwordRootIndex G.rootBase expression j.val.down.val)
        (subwordRootIndex G.rootBase expression j.val.down.val)) =
        -subwordRoot (weylRealization G.rootBase) expression j.val.down.val :=
    (normalizedRoot_neg G.rootBase _).trans
      (congrArg Neg.neg (subwordRoot_eq_normalized G.rootBase expression j.val.down.val).symm)
  have hc := rootCharacter_root_rank G (fun j : A =>
    G.rootSystem.reflectionPerm (subwordRootIndex G.rootBase expression j.val.down.val)
      (subwordRootIndex G.rootBase expression j.val.down.val))
  change Module.finrank ℝ (Submodule.span ℝ (Set.range
    (fun (j : A) (k : G.torusIndex) =>
      ((subwordCharacter G expression j.val.down).toAdd k : ℝ)))) = _ at hc
  have he : Set.range (fun j : A => normalizedRoot G.rootBase
      (G.rootSystem.reflectionPerm (subwordRootIndex G.rootBase expression j.val.down.val)
        (subwordRootIndex G.rootBase expression j.val.down.val))) =
      Set.range (fun j : A =>
        -subwordRoot (weylRealization G.rootBase) expression j.val.down.val) :=
    congrArg Set.range (funext hn)
  have hd := congrArg (fun S : Set (G.rootBase.support →₀ ℝ) =>
    Module.finrank ℝ (Submodule.span ℝ S)) he
  exact hr.trans (hc.trans hd)

/-- General parameters have the full subexpression root-weight span. -/
theorem deodharGeneral_weightSpan
    (x : (deodharParameters G expression).points)
    (hx : x ∈ deodharGeneralParameters G expression) :
    deodharOrbitWeightSpan G expression x =
      subwordWeightSpan (weylRealization G.rootBase) expression :=
  deodharOrbitWeightSpan_eq G expression x hx
end
end SchubertOrbits
