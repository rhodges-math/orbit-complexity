import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyCoxeter
import OrbitComplexity.BruhatIntervals.Words.Subexpression
import OrbitComplexity.GroupActions.Varieties.CoordinateOpens
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties
import OrbitComplexity.GroupActions.Varieties.OpenPoints
import OrbitComplexity.GroupActions.Varieties.AffineDimension

/-! # Geometric Deodhar parameter varieties

Omitted and decreasing positions index affine coordinates. The open subset where omitted
coordinates are nonzero is the parameter variety, with its coordinate inclusion and dimension.
-/

open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety BruhatIntervals
noncomputable section
namespace SchubertGeometry
universe u

private theorem open_points_eq {K : Type u} [Field K] [IsAlgClosed K]
    (X : Variety K) (U : X.scheme.Opens) :
    Set.range (mapPoints (X.openInclusion U)) = {x | X.pointMap x ∈ U} := by
  rw [range_mapPoints, openInclusion_range]
  rfl

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroups.ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- The coordinate positions are the omitted and decreasing steps of the subexpression. -/
abbrev deodharIndex := ULift.{u} {position : Fin word.length //
  position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
    negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression}

private def parameterPositions : Finset (deodharIndex G expression) := by
  classical
  letI : Fintype (deodharIndex G expression) := Fintype.ofFinite _
  exact Finset.univ.filter (fun j : deodharIndex G expression =>
    j.down.val ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression)

private def parameterPolynomial : MvPolynomial (deodharIndex G expression) K :=
  ∏ j ∈ parameterPositions G expression, MvPolynomial.X j

/-- The Deodhar parameter open requires nonzero coordinates at omitted positions. -/
def deodharParameterOpen : (affineSpaceVariety K (deodharIndex G expression)).scheme.Opens :=
  PrimeSpectrum.basicOpen (parameterPolynomial G expression)

private theorem parameter_mem (x : (affineSpaceVariety K (deodharIndex G expression)).points) :
    (affineSpaceVariety K (deodharIndex G expression)).pointMap x ∈
        deodharParameterOpen G expression ↔
      ∀ j : deodharIndex G expression,
        j.down.val ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression →
          affineSpaceVarietyPointsEquiv K (deodharIndex G expression) x j ≠ 0 := by
  classical
  change _ ∈ PrimeSpectrum.basicOpen
    (∏ j ∈ parameterPositions G expression, (MvPolynomial.X j :
      MvPolynomial (deodharIndex G expression) K)) ↔ _
  exact (affineBasicOpen_points (parameterPositions G expression) x).trans (by
    simp only [parameterPositions, Finset.mem_filter, Finset.mem_univ, true_and])

/-- The parameter variety is the open coordinate locus with invertible omitted coordinates. -/
def deodharParameters : Variety K :=
  (affineSpaceVariety K (deodharIndex G expression)).openSubvariety
    (deodharParameterOpen G expression)

/-- The parameter variety includes into affine space by its coordinates. -/
def deodharParameterInclusion :
    (deodharParameters G expression).toOver ⟶
      (affineSpaceVariety K (deodharIndex G expression)).toOver :=
  (affineSpaceVariety K (deodharIndex G expression)).openInclusion
    (deodharParameterOpen G expression)

/-- The coordinate inclusion of the parameter variety is an open immersion. -/
instance deodharParameterInclusion_isOpen :
    IsOpenImmersion (deodharParameterInclusion G expression).left :=
  inferInstanceAs (IsOpenImmersion ((affineSpaceVariety K
    (deodharIndex G expression)).openInclusion (deodharParameterOpen G expression)).left)

/-- The parameter coordinates are exactly the tuples with nonzero omitted entries. -/
theorem deodharParameter_points :
    Set.range (mapPoints (deodharParameterInclusion G expression)) =
      {x | ∀ j : deodharIndex G expression,
        j.down.val ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression →
          affineSpaceVarietyPointsEquiv K (deodharIndex G expression) x j ≠ 0} := by
  exact (open_points_eq (affineSpaceVariety K (deodharIndex G expression))
    (deodharParameterOpen G expression)).trans (Set.ext (parameter_mem G expression))

private theorem parameter_nonempty :
    (deodharParameterOpen G expression : Set
      (affineSpaceVariety K (deodharIndex G expression)).scheme).Nonempty := by
  let x := (affineSpaceVarietyPointsEquiv K (deodharIndex G expression)).symm (fun _ => 1)
  refine ⟨_, (parameter_mem G expression x).mpr ?_⟩
  intro j _
  change affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
    ((affineSpaceVarietyPointsEquiv K (deodharIndex G expression)).symm _) j ≠ 0
  rw [Equiv.apply_symm_apply]
  exact one_ne_zero

/-- The parameter variety is irreducible as a nonempty open subset of affine space. -/
instance deodharParameters_irreducible :
    IrreducibleSpace (deodharParameters G expression).scheme := by
  have hX : IrreducibleSpace (affineSpaceVariety K (deodharIndex G expression)).scheme :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum
      (MvPolynomial (deodharIndex G expression) K)))
  have hU : Nonempty (deodharParameterOpen G expression) :=
    (parameter_nonempty G expression).to_subtype
  change IrreducibleSpace (deodharParameterOpen G expression)
  exact @Topology.IsOpenEmbedding.irreducibleSpace _ _ _ _ _
    (deodharParameterOpen G expression).isOpenEmbedding' hX hU

/-- The parameter variety has one dimension for every omitted or decreasing position. -/
theorem deodharParameters_dim :
    (deodharParameters G expression).dim =
      (Nat.card (deodharIndex G expression) : WithBot ℕ∞) := by
  have : IrreducibleSpace (affineSpaceVariety K (deodharIndex G expression)).scheme :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum
      (MvPolynomial (deodharIndex G expression) K)))
  exact (openSubvariety_dim (affineSpaceVariety K (deodharIndex G expression))
    (deodharParameterOpen G expression) (parameter_nonempty G expression)).trans
      (dim_affineSpaceVariety K (deodharIndex G expression))

/-- The selected coordinate count is the number of omitted steps plus decreasing steps. -/
theorem deodharIndex_card :
    Nat.card (deodharIndex G expression) =
      (equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression).ncard +
        (negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression).ncard := by
  rw [deodharIndex, Nat.card_ulift, Nat.card_coe_set_eq]
  refine Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _)
  rw [Set.disjoint_left]
  intro j he hn
  exact hn.2 he.symm

end SchubertGeometry
