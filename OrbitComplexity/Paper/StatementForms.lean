import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Order.Cover
import OrbitComplexity.BruhatIntervals.Graph.Basic
import OrbitComplexity.BruhatIntervals.Graph.Chains
import OrbitComplexity.BruhatIntervals.Graph.CoverSpans
import OrbitComplexity.BruhatIntervals.Graph.Diamonds
import OrbitComplexity.BruhatIntervals.Graph.Dimension
import OrbitComplexity.BruhatIntervals.Graph.Forks
import OrbitComplexity.BruhatIntervals.Graph.Properties
import OrbitComplexity.BruhatIntervals.Graph.Recursion
import OrbitComplexity.BruhatIntervals.Graph.Support
import OrbitComplexity.BruhatIntervals.Graph.ThinIntervals
import OrbitComplexity.BruhatIntervals.Graph.Toric
import OrbitComplexity.BruhatIntervals.Graph.ToricMaxima
import OrbitComplexity.BruhatIntervals.Intervals.RankTwo
import OrbitComplexity.BruhatIntervals.Order.Basic
import OrbitComplexity.BruhatIntervals.Order.Combinatorics
import OrbitComplexity.BruhatIntervals.Order.Ranks
import OrbitComplexity.BruhatIntervals.Realizations.Products
import OrbitComplexity.BruhatIntervals.ReflectionSubgroups.SpanEquality
import OrbitComplexity.BruhatIntervals.Words.Distinct
import OrbitComplexity.BruhatIntervals.Words.ParabolicDescents
import OrbitComplexity.BruhatIntervals.Words.ParabolicOrder
import OrbitComplexity.BruhatIntervals.Words.Positive
import OrbitComplexity.BruhatIntervals.Words.Subexpression
import OrbitComplexity.BruhatIntervals.Words.Subword
import OrbitComplexity.BruhatIntervals.Words.Support
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties
import OrbitComplexity.GroupActions.Actions.OrbitDimension
import OrbitComplexity.GroupActions.Actions.Stabilizers
import OrbitComplexity.GroupActions.Complexity.Basic
import OrbitComplexity.GroupActions.Complexity.Spherical
import OrbitComplexity.GroupActions.Complexity.TorusBorel
import OrbitComplexity.GroupActions.Rosenlicht.OrbitMaximum
import OrbitComplexity.GroupActions.Rosenlicht.OrbitQuotient
import OrbitComplexity.GroupActions.Rosenlicht.ReductiveComplexity
import OrbitComplexity.GroupActions.Varieties.SpecialLinear
import OrbitComplexity.Paper.BruhatExamples.Boolean
import OrbitComplexity.Paper.BruhatExamples.Induction
import OrbitComplexity.Paper.BruhatExamples.Permutations
import OrbitComplexity.Paper.Complex.Birational
import OrbitComplexity.Paper.Complex.Complexity
import OrbitComplexity.Paper.Complex.DeodharExample
import OrbitComplexity.Paper.Complex.FlagVarieties
import OrbitComplexity.Paper.Complex.InvariantFunctions
import OrbitComplexity.Paper.Complex.OrbitDimension
import OrbitComplexity.Paper.Complex.PartialFlags
import OrbitComplexity.Paper.Complex.PartialSchubert
import OrbitComplexity.Paper.Complex.Products
import OrbitComplexity.Paper.Complex.RootParameters
import OrbitComplexity.Paper.Complex.Spherical
import OrbitComplexity.Paper.Complex.Stabilizer
import OrbitComplexity.Paper.Complex.TwistedCells
import OrbitComplexity.Paper.Deodhar.Characters
import OrbitComplexity.Paper.Deodhar.ComponentStandardForms
import OrbitComplexity.Paper.Deodhar.ComponentWeights
import OrbitComplexity.Paper.Deodhar.FibreFlags
import OrbitComplexity.Paper.Deodhar.GL3OrbitDimensions
import OrbitComplexity.Paper.Deodhar.GL3Weyl
import OrbitComplexity.Paper.Deodhar.GeneralParameters
import OrbitComplexity.Paper.Deodhar.MaximalWeights
import OrbitComplexity.Paper.Deodhar.ParameterComplexity
import OrbitComplexity.Paper.Deodhar.ParameterPrefixes
import OrbitComplexity.Paper.Deodhar.ParameterProduct
import OrbitComplexity.Paper.Deodhar.Parameters
import OrbitComplexity.Paper.Deodhar.Products
import OrbitComplexity.Paper.Deodhar.RootIndices
import OrbitComplexity.Paper.Deodhar.Roots
import OrbitComplexity.Paper.Deodhar.Spans
import OrbitComplexity.Paper.Deodhar.SubwordRootSubgroups
import OrbitComplexity.Paper.Deodhar.WeightRank
import OrbitComplexity.Paper.Heart.CellAffine
import OrbitComplexity.Paper.Heart.CodimensionBounds
import OrbitComplexity.Paper.Heart.ComplementEquivalences
import OrbitComplexity.Paper.Heart.ComplementStatements
import OrbitComplexity.Paper.Heart.Decomposition
import OrbitComplexity.Paper.Heart.DefinitionStatements
import OrbitComplexity.Paper.Heart.DynamicsStatements
import OrbitComplexity.Paper.Heart.Isomorphism
import OrbitComplexity.Paper.Heart.LeviBorel
import OrbitComplexity.Paper.Heart.LeviBorelComplement
import OrbitComplexity.Paper.Heart.LeviComplexityFormula
import OrbitComplexity.Paper.Heart.LeviMinimum
import OrbitComplexity.Paper.Heart.LeviOrbitDimension
import OrbitComplexity.Paper.Heart.LeviOrbitStatements
import OrbitComplexity.Paper.Heart.Meeting
import OrbitComplexity.Paper.Heart.OrbitCodimension
import OrbitComplexity.Paper.Heart.SchubertOrbits
import OrbitComplexity.Paper.Heart.TorusCodimension
import OrbitComplexity.Paper.Heart.TwistedComplex
import OrbitComplexity.Paper.RichardsonComplexity
import OrbitComplexity.Paper.Roots.Definition
import OrbitComplexity.Paper.Roots.Products
import OrbitComplexity.Paper.ToricComplexity
import OrbitComplexity.SchubertGeometry.Cells.CellAffine
import OrbitComplexity.SchubertGeometry.Cells.ClosureStability
import OrbitComplexity.SchubertGeometry.Cells.OrbitDecomposition
import OrbitComplexity.SchubertGeometry.Cells.RichardsonActions
import OrbitComplexity.SchubertGeometry.Cells.RichardsonStructure
import OrbitComplexity.SchubertGeometry.Deodhar.ComponentDecomposition
import OrbitComplexity.SchubertGeometry.Deodhar.PositiveComponent
import OrbitComplexity.SchubertGeometry.Deodhar.StandardFormVariety
import OrbitComplexity.SchubertGeometry.FlagVariety.PointTopology
import OrbitComplexity.SchubertGeometry.Groups.WeylQuotient
import OrbitComplexity.SchubertGeometry.Parabolics.EmptyLevi
import OrbitComplexity.SchubertGeometry.Parabolics.ProjectionActions
import OrbitComplexity.SchubertGeometry.Parabolics.Proper
import OrbitComplexity.SchubertGeometry.Parabolics.Schubert
import OrbitComplexity.SchubertGeometry.Parabolics.StabilizerOrder
import OrbitComplexity.SchubertGeometry.Parabolics.Structure
import OrbitComplexity.SchubertGeometry.Parabolics.TorusActions
import OrbitComplexity.SchubertGeometry.Roots.Subgroups

/-! # Statement forms of combined index entries

Several index entries and supporting statements combine clauses proved in different modules.
Each theorem below states one of them in full, in the form of the paper.

## Main results

* `SchubertOrbits.deodharStandardForm_definition`: Definition 3.16, the standard form, its
  coordinates and its isomorphism with the Deodhar component.
* `SchubertOrbits.deodharStandard_partition`: Theorem 3.17, the Deodhar components partition the
  open Richardson variety.
* `SchubertOrbits.subwordRoot_labels`, `SchubertOrbits.subwordWeight_definitions`,
  `SchubertOrbits.subwordWeight_recurrence`: the clauses of Definition 3.19.
-/

namespace SchubertOrbits

section Combinatorics
open BruhatIntervals

/-- The combinatorial root clauses of Definition 3.19: the two sign cases and their positive
Bruhat edge labels. -/
theorem subwordRoot_labels :
    ∀ {S W V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
      [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V))
      {word : List S} (expression : Subexpression word), IsDistinguished cs expression →
      ∀ j : Fin word.length,
      (j ∈ equalSteps cs expression → SchubertOrbits.subwordRoot realization expression j =
        realization.action (expression.prefixProd cs j.val)
          (realization.simpleRoot word[j.val])) ∧
      (j ∈ negativeSteps cs expression → SchubertOrbits.subwordRoot realization expression j =
        -realization.action (expression.prefixProd cs j.val)
          (realization.simpleRoot word[j.val])) ∧
      (j ∈ equalSteps cs expression ∨ j ∈ negativeSteps cs expression →
        SchubertOrbits.subwordRoot realization expression j ∈ realization.positiveRoots ∧
        SchubertOrbits.subwordRoot realization expression j = edgeLabel realization
          (expression.prefixProd cs j.val)
          (expression.prefixProd cs j.val * cs.simple word[j.val])
          ((cs.isReflection_simple word[j.val]).conj (expression.prefixProd cs j.val))) := by
  intro S W V _ M cs _ _ realization word expression hd j
  refine ⟨SchubertOrbits.subwordRoot_of_equal realization expression j,
    SchubertOrbits.subwordRoot_of_negative realization expression j, ?_⟩
  intro hj
  exact ⟨SchubertOrbits.subwordRoot_positive realization expression hd j hj,
    SchubertOrbits.subwordRoot_eq_edgeLabel realization expression hd j hj⟩

/-- The combinatorial span clauses of Definition 3.19: the finite-dimensional real span, its
dimension, and its equality with the span of the negative roots. -/
theorem subwordWeight_definitions :
    ∀ {S W V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
      [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V))
      {word : List S} (expression : Subexpression word),
      SchubertOrbits.subwordWeightSpan realization expression = Submodule.span ℝ
        ((SchubertOrbits.subwordRoot realization expression) ''
          (equalSteps cs expression ∪ negativeSteps cs expression)) ∧
      FiniteDimensional ℝ (SchubertOrbits.subwordWeightSpan realization expression) ∧
      SchubertOrbits.subwordWeightDim realization expression =
        Module.finrank ℝ (SchubertOrbits.subwordWeightSpan realization expression) ∧
      SchubertOrbits.subwordWeightSpan realization expression = Submodule.span ℝ
        ((fun j => -SchubertOrbits.subwordRoot realization expression j) ''
          (equalSteps cs expression ∪ negativeSteps cs expression)) := by
  intro S W V _ M cs _ _ realization word expression
  exact ⟨rfl, inferInstance, rfl, SchubertOrbits.subwordWeightSpan_eq_neg realization expression⟩

/-- Prefixes of subexpressions have the truncated choices and factors, the same initial
products, and inherited distinguished and positive conditions. -/
theorem subexpression_prefixes :
    ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
      {word : List S} (expression : Subexpression word) (n k : ℕ),
      (expression.take n).choices = expression.choices.take n ∧
      (expression.take n).factors cs = (expression.factors cs).take n ∧
      (expression.take n).prefixProd cs k = expression.prefixProd cs (min k n) ∧
      (IsDistinguished cs expression → IsDistinguished cs (expression.take n)) ∧
      (IsPositive cs expression → IsPositive cs (expression.take n)) := by
  intro S W _ M cs word expression n k
  exact ⟨rfl, expression.factors_take cs n, expression.prefixProd_take cs n k,
    fun hd => hd.take cs n, fun hp => hp.take cs n⟩

/-- The last-position recurrence for the subword weight span: an increasing position preserves
the span, and an omitted or decreasing position adds its root line. -/
theorem subwordWeight_recurrence :
    ∀ {S W V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
      [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V))
      {word : List S} (expression : Subexpression word) (j : Fin word.length),
      j.val + 1 = word.length →
      (j ∈ positiveSteps cs expression →
        SchubertOrbits.subwordWeightSpan realization expression =
          SchubertOrbits.subwordWeightSpan realization (expression.take j.val)) ∧
      (j ∈ equalSteps cs expression ∪ negativeSteps cs expression →
        SchubertOrbits.subwordWeightSpan realization expression =
          SchubertOrbits.subwordWeightSpan realization (expression.take j.val) ⊔
            Submodule.span ℝ {SchubertOrbits.subwordRoot realization expression j}) := by
  intro S W V _ M cs _ _ realization word expression j hlast
  exact ⟨SchubertOrbits.subwordWeightSpan_last_positive realization expression j hlast,
    SchubertOrbits.subwordWeightSpan_last realization expression j hlast⟩

/-- The lower interval at the identity has its simple-root support span and support
cardinality. -/
theorem lower_support_span :
    ∀ {S W V : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
      [AddCommGroup V] [Module ℝ V] (realization : Realization cs (V := V)) (w : W),
      labelSpan realization 1 w = Submodule.span ℝ
        (realization.simpleRoot '' {i : S | cs.BruhatLE (cs.simple i) w}) ∧
      algebraicDim realization 1 w = supportCard cs w := by
  intro S W V _ M cs _ _ realization w
  exact ⟨BruhatIntervals.labelSpan_one realization w,
    BruhatIntervals.algebraicDim_one realization w⟩

end Combinatorics

section Orbits
open CategoryTheory AlgebraicGeometry GroupActions

/-- The irreducible-group form of the orbit-dimension formula: the rational orbit is locally
closed, and its dimension is the group dimension minus the stabilizer dimension. -/
@[nolint unusedArguments]
theorem orbit_dimension_irreducible :
    ∀ {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
      (H X : Variety K) [GrpObj H.toOver] [ModObj H.toOver X.toOver]
      [IrreducibleSpace H.scheme] (x : X.points),
      IsLocallyClosed (MulAction.orbit H.points x) ∧
        (orbitNatDim H X x : ℤ) = (H.natDim : ℤ) -
          ((stabilizerVariety H X x).natDim : ℤ) := by
  intro K _ _ _ H X _ _ _ x
  refine ⟨GroupActions.orbit_locallyClosed H X x, ?_⟩
  have h := congrArg (fun n : ℕ ↦ (n : ℤ)) (GroupActions.orbitNatDim_add_stabilizer H X x)
  rw [Nat.cast_add] at h
  exact eq_sub_iff_add_eq.mpr h.symm

end Orbits

section Parameters
open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open BruhatIntervals ReductiveGroups GroupActions GroupActions.Variety SchubertGeometry

/-- The coordinate-open, dimension and character-action clauses of the parameter variety. -/
theorem deodharParameter_variety :
    ∀ {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
      (G : ReductiveGroupData K) {word : List G.rootBase.support}
      (expression : Subexpression word),
      IsOpenImmersion (deodharParameterInclusion G expression).left ∧
      Set.range (mapPoints (deodharParameterInclusion G expression)) =
        {x | ∀ j : deodharIndex G expression,
          j.down.val ∈ equalSteps (weylCoxeterSystem G.rootBase) expression →
            affineSpaceVarietyPointsEquiv K (deodharIndex G expression) x j ≠ 0} ∧
      IrreducibleSpace (deodharParameters G expression).scheme ∧
      (deodharParameters G expression).dim =
        (((equalSteps (weylCoxeterSystem G.rootBase) expression).ncard +
          (negativeSteps (weylCoxeterSystem G.rootBase) expression).ncard : ℕ) :
            WithBot ℕ∞) ∧
      (letI := deodharParameterAction G expression
       ∀ (t : (torusVariety G).points) (x : (deodharParameters G expression).points)
         (j : deodharIndex G expression),
         affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
             (mapPoints (deodharParameterInclusion G expression) (t • x)) j =
           affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
             (mapPoints (deodharParameterInclusion G expression) x) j *
               affinePointsEquiv.symm t ((torusCoordinateEquiv G).symm
                 (MonoidAlgebra.single (subwordCharacter G expression j.down) 1))) := by
  intro K _ _ _ G word expression
  refine ⟨inferInstance, SchubertOrbits.deodharParameter_points G expression,
    inferInstance, ?_, ?_⟩
  · exact (SchubertOrbits.deodharParameters_dim G expression).trans
      (congrArg (fun n : ℕ => (n : WithBot ℕ∞)) (SchubertOrbits.deodharIndex_card G expression))
  · exact fun t x j => SchubertOrbits.deodharParameter_smul G expression t x j

/-- The parameter variety is a split torus times an affine space, with the numbers of omitted
and decreasing positions as their dimensions. -/
theorem deodharParameter_product :
    ∀ {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
      (G : ReductiveGroupData K) {word : List G.rootBase.support}
      (expression : Subexpression word),
      Nonempty ((deodharParameters G expression).toOver ≅
        (reductiveVariety (SplitTorus.groupData K (deodharEqualPositions G expression))).toOver ⊗
          (affineSpaceVariety K {j : deodharIndex G expression //
            j ∉ deodharEqualPositions G expression}).toOver) ∧
      Nat.card (deodharEqualPositions G expression) =
        (equalSteps (weylCoxeterSystem G.rootBase) expression).ncard ∧
      Nat.card {j : deodharIndex G expression // j ∉ deodharEqualPositions G expression} =
        (negativeSteps (weylCoxeterSystem G.rootBase) expression).ncard := by
  intro K _ _ _ G word expression
  exact ⟨⟨SchubertOrbits.deodharParameterProductIso G expression⟩,
    SchubertOrbits.deodharParameterProduct_counts G expression⟩

end Parameters

section StandardForms
open CategoryTheory AlgebraicGeometry BruhatIntervals ReductiveGroups
open GroupActions MonoidalCategory SchubertGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)
  (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
  (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)

private theorem step_formula (p : Fin word.length → K) (j : Fin word.length) :
    deodharStep G expression p j =
      if j ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression then
        gaParameterPoint (G.simpleRootMap (word.get j)) (p j) *
          (simpleRepresentative G (word.get j))⁻¹
      else if j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression then
        gaParameterPoint (G.negativeSimpleRootMap (word.get j)) (p j)
      else simpleRepresentative G (word.get j) := by
  classical
  by_cases hn : j ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression
  · simp only [deodharStep, deodharRootElement, subwordStepPoint, hn, ↓reduceIte,
      List.get_eq_getElem]
  · by_cases he : j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression
    · simp only [deodharStep, deodharRootElement, subwordStepPoint, hn, he, ↓reduceIte,
        List.get_eq_getElem, mul_one]
    · simp only [deodharStep, deodharRootElement, subwordStepPoint, hn, he, ↓reduceIte,
        List.get_eq_getElem, one_mul]

private theorem prefix_formula (p : Fin word.length → K) :
    deodharPrefix G expression p word.length =
      (List.ofFn (fun j : Fin word.length =>
        if j ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression then
          gaParameterPoint (G.simpleRootMap (word.get j)) (p j) *
            (simpleRepresentative G (word.get j))⁻¹
        else if j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression then
          gaParameterPoint (G.negativeSimpleRootMap (word.get j)) (p j)
        else simpleRepresentative G (word.get j))).prod := by
  have h := funext (step_formula G expression p)
  unfold deodharPrefix
  have hlen : (List.ofFn (deodharStep G expression p)).length ≤ word.length := by
    simp only [List.length_ofFn, le_refl]
  rw [List.take_of_length_le hlen]
  exact congrArg (fun f : Fin word.length → G.points => (List.ofFn f).prod) h

/-- Definition 3.16: the standard form is a locally closed subvariety of `G` whose points are the
products of the root factors and signed simple representatives, with the omitted coordinates
nonzero. It is a split torus times an affine space, and it is isomorphic to the Deodhar
component over the flag variety. -/
theorem deodharStandardForm_definition :
    IsImmersion (deodharStandardInclusion G expression hred hd).left ∧
    Set.range (fun x : (deodharStandardVariety G expression hred hd).points =>
      (reductivePointsEquiv G).symm
        (Variety.mapPoints (deodharStandardInclusion G expression hred hd) x)) =
      {g | ∃ p : Fin word.length → K,
        (∀ j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression, p j ≠ 0) ∧
          (List.ofFn (fun j : Fin word.length =>
            if j ∈ negativeSteps (weylCoxeterSystem G.rootBase) expression then
              gaParameterPoint (G.simpleRootMap (word.get j)) (p j) *
                (simpleRepresentative G (word.get j))⁻¹
            else if j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression then
              gaParameterPoint (G.negativeSimpleRootMap (word.get j)) (p j)
            else simpleRepresentative G (word.get j))).prod = g} ∧
    Nonempty ((deodharStandardVariety G expression hred hd).toOver ≅
      (reductiveVariety (SplitTorus.groupData K
        (deodharEqualPositions G expression))).toOver ⊗
          (affineSpaceVariety K {j : deodharIndex G expression //
            j ∉ deodharEqualPositions G expression}).toOver) ∧
    (Nat.card (deodharEqualPositions G expression) =
      (equalSteps (weylCoxeterSystem G.rootBase) expression).ncard ∧
      Nat.card {j : deodharIndex G expression // j ∉ deodharEqualPositions G expression} =
        (negativeSteps (weylCoxeterSystem G.rootBase) expression).ncard) ∧
    ∃ e : (deodharStandardVariety G expression hred hd).toOver ≅
        (deodharComponent G expression hred).toOver,
      e.hom ≫ deodharInclusion G expression hred =
        deodharStandardInclusion G expression hred hd ≫ flagQuotientMorphism G := by
  refine ⟨?_, ?_, ⟨deodharStandardProductIso G expression hred hd⟩,
    deodharParameterProduct_counts G expression,
    deodharStandardComponentIso G expression hred hd,
    deodharStandardComponentIso_quotient G expression hred hd⟩
  · change IsImmersion ((reductiveVariety G).locallyClosedInclusion _ _).left
    infer_instance
  · refine (deodharStandard_points G expression hred hd).trans ?_
    ext g
    constructor
    · rintro ⟨p, hp, he⟩
      exact ⟨p, hp, (prefix_formula G expression p).symm.trans he⟩
    · rintro ⟨p, hp, he⟩
      exact ⟨p, hp, (prefix_formula G expression p).trans he⟩

/-- Theorem 3.17: the Deodhar components of the distinguished subexpressions with product `v`
partition the open Richardson variety, and every point lies in exactly one of them. -/
theorem deodharStandard_partition (v : G.weylGroup) :
    ((⋃ e : {e : Subexpression word // IsDistinguished (weylCoxeterSystem G.rootBase) e ∧
        e.prefixProd (weylCoxeterSystem G.rootBase) word.length = v},
      Set.range (deodharStandardInclusion G e.val hred e.property.1 ≫
        flagQuotientMorphism G).left) =
          Set.range (richardsonCellInclusion G v (simpleWeylWord G.rootBase word)).left ∧
    Pairwise (fun a b : {e : Subexpression word //
        IsDistinguished (weylCoxeterSystem G.rootBase) e ∧
          e.prefixProd (weylCoxeterSystem G.rootBase) word.length = v} =>
      Disjoint (Set.range (deodharStandardInclusion G a.val hred a.property.1 ≫
        flagQuotientMorphism G).left)
        (Set.range (deodharStandardInclusion G b.val hred b.property.1 ≫
          flagQuotientMorphism G).left))) ∧
    ∀ (x : (flagVariety G).scheme)
      (_hx : x ∈ Set.range
        (richardsonCellInclusion G v (simpleWeylWord G.rootBase word)).left),
    ∃! e : {e : Subexpression word // IsDistinguished (weylCoxeterSystem G.rootBase) e ∧
        e.prefixProd (weylCoxeterSystem G.rootBase) word.length = v},
      x ∈ Set.range (deodharStandardInclusion G e.val hred e.property.1 ≫
        flagQuotientMorphism G).left :=
  ⟨deodharStandard_decomposition G hred v, deodharStandard_unique G hred v⟩

end
end StandardForms

section Hearts
open CategoryTheory AlgebraicGeometry ReductiveGroups GroupActions SchubertGeometry

/-- The heart stabilizer equality and the corresponding orbit dimension shift. -/
theorem heart_stabilizer_dimension (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∀ (G : ReductiveGroupData K) (I : Set G.rootBase.support) (w : G.weylGroup)
      (_ : ∀ i ∈ I, ¬ G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w⁻¹ i))
      (h : (SchubertOrbits.heart G I w).points),
      Set.range (Variety.mapPoints
        (stabilizerInclusion (torusVariety G) (SchubertOrbits.heart G I w) h ≫
          torusLeviBorelInclusion G I)) =
        Set.range (Variety.mapPoints (stabilizerInclusion (leviBorelVariety G I)
          (schubertCell G w) (Variety.mapPoints (SchubertOrbits.heartCellInclusion G I w) h))) ∧
      orbitNatDim (leviBorelVariety G I) (schubertCell G w)
          (Variety.mapPoints (SchubertOrbits.heartCellInclusion G I w) h) =
        (weylCoxeterSystem G.rootBase).length (leftParabolicFactor G.rootBase I w) +
          orbitNatDim (torusVariety G) (SchubertOrbits.heart G I w) h := by
  intro G I w hI h
  exact ⟨SchubertOrbits.heartStabilizer_range G I w hI h,
    SchubertOrbits.heartLeviOrbitDim G I w hI h⟩

end Hearts

section ComplexityFormulas
open BruhatIntervals ReductiveGroups GroupActions SchubertGeometry
universe w
variable {K : Type w} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

/-- Theorem 1.2: the torus complexity of a Richardson variety is `ℓ(v) - ℓ(u) - ad(u, v)`, and
`ad(u, v)` is the largest dimension of a toric Richardson variety `R_{w,v}` with
`u ≤ w ≤ v`. -/
theorem richardson_complexity_formula (u v : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE u v) :
    (torusComplexity G (richardsonVariety G u v) : ℤ) =
      ((weylCoxeterSystem G.rootBase).length v : ℤ) - (weylCoxeterSystem G.rootBase).length u -
        algebraicDim (weylRealization G.rootBase) u v ∧
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval (weylCoxeterSystem G.rootBase) u v,
      IsToricVariety G (richardsonVariety G w v) ∧
        (weylCoxeterSystem G.rootBase).length v - (weylCoxeterSystem G.rootBase).length w = n}
      (algebraicDim (weylRealization G.rootBase) u v) := by
  obtain ⟨h, hmax⟩ := richardson_complexity_and_max G u v hle
  have h1 := algebraicDim_le_length (weylRealization G.rootBase) u v hle
  have h2 := hle.length_le
  exact ⟨by omega, hmax⟩

/-- Theorem 1.2 over the complex numbers, proved through the moment-map description of the
maximal torus orbits. -/
theorem richardson_complexity_formula_complex (G : ReductiveGroupData ℂ) (u v : G.weylGroup)
    (hle : (weylCoxeterSystem G.rootBase).BruhatLE u v) :
    (torusComplexity G (richardsonVariety G u v) : ℤ) =
      ((weylCoxeterSystem G.rootBase).length v : ℤ) - (weylCoxeterSystem G.rootBase).length u -
        algebraicDim (weylRealization G.rootBase) u v ∧
    IsGreatest {n : ℕ | ∃ w ∈ bruhatInterval (weylCoxeterSystem G.rootBase) u v,
      IsToricVariety G (richardsonVariety G w v) ∧
        (weylCoxeterSystem G.rootBase).length v - (weylCoxeterSystem G.rootBase).length w = n}
      (algebraicDim (weylRealization G.rootBase) u v) := by
  obtain ⟨h, hmax⟩ := richardson_complexity_and_max_complex G u v hle
  have h1 := algebraicDim_le_length (weylRealization G.rootBase) u v hle
  have h2 := hle.length_le
  exact ⟨by omega, hmax⟩

/-- Corollary 1.3: the torus complexity of a Schubert variety is `ℓ(w) - |supp(w)|`. -/
theorem schubert_complexity_formula (w : G.weylGroup) :
    (torusComplexity G (schubertVariety G w) : ℤ) =
      ((weylCoxeterSystem G.rootBase).length w : ℤ) -
        supportCard (weylCoxeterSystem G.rootBase) w := by
  have h := schubert_torus_complexity G w
  have h1 := algebraicDim_le_length (weylRealization G.rootBase) 1 w
    ((weylCoxeterSystem G.rootBase).one_bruhatLE w)
  rw [algebraicDim_one, (weylCoxeterSystem G.rootBase).length_one] at h1
  omega

/-- Corollary 1.3 over the complex numbers. -/
theorem schubert_complexity_formula_complex (G : ReductiveGroupData ℂ) (w : G.weylGroup) :
    (torusComplexity G (schubertVariety G w) : ℤ) =
      ((weylCoxeterSystem G.rootBase).length w : ℤ) -
        supportCard (weylCoxeterSystem G.rootBase) w := by
  have h := schubert_torus_complexity_complex G w
  have h1 := algebraicDim_le_length (weylRealization G.rootBase) 1 w
    ((weylCoxeterSystem G.rootBase).one_bruhatLE w)
  rw [algebraicDim_one, (weylCoxeterSystem G.rootBase).length_one] at h1
  omega

end ComplexityFormulas

section PartialSchubert
open CategoryTheory GroupActions ReductiveGroups SchubertGeometry
universe v
variable {K : Type v} [Field K] [IsAlgClosed K] [CharZero K]

/-- The induced torus action on a Schubert variety in a partial flag variety is equivariant and
has the torus complexity of the corresponding Schubert variety in `G/B`. -/
theorem partialSchubert_torus (G : ReductiveGroupData K) (J : Set G.rootBase.support)
    (w : G.weylGroup) (hw : IsMinimalRightParabolic G.rootBase J w) :
    letI := Mod.scalarRestriction (torusInclusion G) (partialFlagVariety G J).toOver
    letI := partialSchubertTorusAction G J w hw
    IsModHom (torusVariety G).toOver (partialSchubertInclusion G J w) ∧
      torusComplexity G (partialSchubertVariety G J w) =
        torusComplexity G (schubertVariety G w) :=
  ⟨SchubertGeometry.partialSchubertTorusEquivariant G J w hw,
    SchubertGeometry.partial_torus_complexity G J w hw⟩

end PartialSchubert

end SchubertOrbits
