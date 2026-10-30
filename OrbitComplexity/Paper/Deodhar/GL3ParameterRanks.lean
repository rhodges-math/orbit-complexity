import OrbitComplexity.Paper.Deodhar.GL3Weights
import OrbitComplexity.Paper.Deodhar.GL3Subwords
import OrbitComplexity.Paper.Deodhar.ParameterOrbits
import OrbitComplexity.Paper.Deodhar.ComponentWeights
import OrbitComplexity.Paper.Deodhar.ComponentOrbitDimensions
import OrbitComplexity.Paper.Deodhar.Scaling
import OrbitComplexity.BruhatIntervals.Permutations.PositiveRoots
import OrbitComplexity.ReductiveGroups.GLn.GroupData
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootData
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Classification
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupBorelTangent
import OrbitComplexity.ReductiveGroups.Groups.Reductive.CharacterRelations
import OrbitComplexity.ReductiveGroups.Roots.Coxeter.PresentationWordPropertyLength
import OrbitComplexity.BruhatIntervals.Words.Subexpression
import OrbitComplexity.SchubertGeometry.Deodhar.StandardFormVariety
import OrbitComplexity.Paper.Deodhar.RootMaps
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaMatrixDifferential
import Mathlib.Tactic

/-! # Parameter orbit dimensions in rank three -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open ReductiveGroups.GLn
open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open SchubertGeometry BruhatIntervals
open scoped Classical

noncomputable section
namespace SchubertOrbits.GL3
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- The two coordinate-difference weights of s₁1s₁. -/
def decreasingWeights : Fin 2 → Fin 3 → ℝ :=
  ![BruhatIntervals.TypeA.root 2 2 0, BruhatIntervals.TypeA.root 2 1 0]

private def positivePair : Fin 2 → Fin 3 → ℝ :=
  ![BruhatIntervals.TypeA.root 2 1 0, BruhatIntervals.TypeA.root 2 2 1]

/-- The three coordinate-difference weights of 111. -/
def positiveWeights : Fin 3 → Fin 3 → ℝ :=
  ![BruhatIntervals.TypeA.root 2 1 0, BruhatIntervals.TypeA.root 2 2 1,
    BruhatIntervals.TypeA.root 2 1 0]

private theorem decreasing_independent : LinearIndependent ℝ decreasingWeights := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have hv := congrFun h 1
    norm_num [decreasingWeights, BruhatIntervals.TypeA.root] at hv
  · intro a h
    have hv := congrFun h 2
    norm_num [decreasingWeights, BruhatIntervals.TypeA.root] at hv

private theorem positive_independent : LinearIndependent ℝ positivePair := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have hv := congrFun h 2
    norm_num [positivePair, BruhatIntervals.TypeA.root] at hv
  · intro a h
    have hv := congrFun h 0
    norm_num [positivePair, BruhatIntervals.TypeA.root] at hv

/-- The two displayed weights of s₁1s₁ span a two-dimensional real space. -/
theorem decreasing_rank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range decreasingWeights)) = 2 := by
  simpa only [Fintype.card_fin] using finrank_span_eq_card decreasing_independent

private theorem positive_range : Set.range positiveWeights = Set.range positivePair := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- The displayed weights of 111 span a two-dimensional real space. -/
theorem positive_rank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range positiveWeights)) = 2 := by
  rw [positive_range]
  simpa only [Fintype.card_fin] using finrank_span_eq_card positive_independent

private theorem decreasing_active_rank {K : Type*} [Field K] (p m : K) (hp : p ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i : {i : Fin 2 // (![p, m] : Fin 2 → K) i ≠ 0} =>
        decreasingWeights i.val))) = if m = 0 then 1 else 2 := by
  classical
  by_cases hm : m = 0
  · have hs : Set.range (fun i : {i : Fin 2 // (![p, m] : Fin 2 → K) i ≠ 0} =>
          decreasingWeights i.val) = {decreasingWeights 0} := by
      ext v
      constructor
      · rintro ⟨⟨i, hi⟩, rfl⟩
        fin_cases i
        · rfl
        · change m ≠ 0 at hi
          exact (hi hm).elim
      · intro hv
        rw [Set.mem_singleton_iff] at hv
        subst v
        exact ⟨⟨0, hp⟩, rfl⟩
    rw [ite_eq_left hm, hs]
    apply finrank_span_singleton
    intro h
    have hv := congrFun h 2
    norm_num [decreasingWeights, BruhatIntervals.TypeA.root] at hv
  · have hs : Set.range (fun i : {i : Fin 2 // (![p, m] : Fin 2 → K) i ≠ 0} =>
          decreasingWeights i.val) = Set.range decreasingWeights := by
      ext v
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, rfl⟩
      · rintro ⟨i, rfl⟩
        have hi : (![p, m] : Fin 2 → K) i ≠ 0 := by
          fin_cases i
          · exact hp
          · exact hm
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [ite_eq_right hm, hs, decreasing_rank]

private theorem lifted_span_rank {ι : Type*} (v : ι → Fin 3 → ℝ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i (j : ULift.{u} (Fin 3)) => v i j.down))) =
      Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := by
  let e : (Fin 3 → ℝ) ≃ₗ[ℝ] (ULift.{u} (Fin 3) → ℝ) :=
    LinearEquiv.funCongrLeft ℝ ℝ Equiv.ulift
  have hs : Submodule.span ℝ (Set.range
      (fun i (j : ULift.{u} (Fin 3)) => v i j.down)) =
      (Submodule.span ℝ (Set.range v)).map e.toLinearMap := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hs]
  exact LinearEquiv.finrank_map_eq e _

private theorem decreasing_lifted_rank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i (j : ULift.{u} (Fin 3)) => decreasingWeights i j.down))) = 2 :=
  (lifted_span_rank decreasingWeights).trans decreasing_rank

private theorem positive_lifted_rank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i (j : ULift.{u} (Fin 3)) => positiveWeights i j.down))) = 2 :=
  (lifted_span_rank positiveWeights).trans positive_rank

private theorem decreasing_lifted_active_rank {K : Type*} [Field K]
    (p m : K) (hp : p ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i : {i : Fin 2 // (![p, m] : Fin 2 → K) i ≠ 0} =>
        fun j : ULift.{u} (Fin 3) => decreasingWeights i.val j.down))) =
      if m = 0 then 1 else 2 :=
  (lifted_span_rank _).trans (decreasing_active_rank p m hp)

private theorem character_real (i j : Fin 3) :
    (fun k : ULift.{u} (Fin 3) => ((matrixUnitWeight i j).toAdd k : ℝ)) =
      (fun k : ULift.{u} (Fin 3) => BruhatIntervals.TypeA.root 2 i j k.down) := by
  funext k
  rcases k with ⟨k⟩
  rw [toAdd_matrixUnitWeight_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [BruhatIntervals.TypeA.root, Pi.single_apply]

/-- A selected parameter coordinate in the rank-three word. -/
def parameterCoordinate (e : Subexpression (matrixWord (K := K)))
    (x : (SchubertGeometry.deodharParameters (GLn.groupData K 3) e).points)
    (j : SchubertGeometry.deodharIndex (GLn.groupData K 3) e) : K :=
  GroupActions.affineSpaceVarietyPointsEquiv K (SchubertGeometry.deodharIndex
    (GLn.groupData K 3) e) (GroupActions.Variety.mapPoints
      (X := SchubertGeometry.deodharParameters (GLn.groupData K 3) e)
      (Y := GroupActions.affineSpaceVariety K
        (SchubertGeometry.deodharIndex (GLn.groupData K 3) e))
      (SchubertGeometry.deodharParameterInclusion (GLn.groupData K 3) e) x) j

/-- The real character vector of a selected parameter in the rank-three word. -/
def parameterWeight (e : Subexpression (matrixWord (K := K)))
    (j : SchubertGeometry.deodharIndex (GLn.groupData K 3) e) :
    ULift.{u} (Fin 3) → ℝ :=
  fun k => ((SchubertOrbits.subwordCharacter (GLn.groupData K 3) e j.down).toAdd k : ℝ)

private theorem decreasing_index_cases
    (j : SchubertGeometry.deodharIndex (GLn.groupData K 3) decreasingExpression) :
    j = ⟨decreasingJ1⟩ ∨ j = ⟨decreasingJ2⟩ := by
  have hj := j.down.property
  rcases hj with he | hn
  · have h1 := (Set.ext_iff.mp (decreasing_equal (K := K)) j.down.val).mp he
    left
    apply ULift.ext
    apply Subtype.ext
    exact Set.mem_singleton_iff.mp h1
  · have h2 := (Set.ext_iff.mp (decreasing_negative (K := K)) j.down.val).mp hn
    right
    apply ULift.ext
    apply Subtype.ext
    exact Set.mem_singleton_iff.mp h2

private theorem positive_index_eq
    (j : SchubertGeometry.deodharIndex (GLn.groupData K 3) positiveExpression) :
    j = ⟨positiveJ j.down.val⟩ := by
  apply ULift.ext
  apply Subtype.ext
  rfl

private theorem decreasing_weight1 :
    parameterWeight (K := K) decreasingExpression ⟨decreasingJ1⟩ =
      fun k : ULift.{u} (Fin 3) => decreasingWeights 0 k.down := by
  unfold parameterWeight
  rw [decreasing_character1]
  exact character_real 2 0

private theorem decreasing_weight2 :
    parameterWeight (K := K) decreasingExpression ⟨decreasingJ2⟩ =
      fun k : ULift.{u} (Fin 3) => decreasingWeights 1 k.down := by
  unfold parameterWeight
  rw [decreasing_character2]
  exact character_real 1 0

private theorem positive_weight (j : Fin 3) :
    parameterWeight (K := K) positiveExpression ⟨positiveJ j⟩ =
      fun k : ULift.{u} (Fin 3) => positiveWeights j k.down := by
  unfold parameterWeight
  rw [positive_character]
  fin_cases j
  · exact character_real 1 0
  · exact character_real 2 1
  · exact character_real 1 0

private theorem coordinate_omitted_nonzero
    (e : Subexpression (matrixWord (K := K)))
    (x : (SchubertGeometry.deodharParameters (GLn.groupData K 3) e).points)
    (j : SchubertGeometry.deodharIndex (GLn.groupData K 3) e)
    (hj : j.down.val ∈ equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase) e) :
    parameterCoordinate e x j ≠ 0 := by
  exact (SchubertGeometry.deodharParameter_points (GLn.groupData K 3) e).subset
    ⟨x, rfl⟩ j hj

/-- The s₁1s₁ parameter orbit has dimension one or two according to its last coordinate. -/
theorem decreasing_parameter_rank
    (x : (SchubertGeometry.deodharParameters (GLn.groupData K 3) decreasingExpression).points) :
    let := SchubertOrbits.deodharParameterAction (GLn.groupData K 3) decreasingExpression
    GroupActions.orbitNatDim (GroupActions.torusVariety (GLn.groupData K 3))
      (SchubertGeometry.deodharParameters (GLn.groupData K 3) decreasingExpression) x =
      if parameterCoordinate decreasingExpression x ⟨decreasingJ2⟩ = 0 then 1 else 2 := by
  classical
  let G := GLn.groupData K 3
  let e := decreasingExpression (K := K)
  let := SchubertOrbits.deodharParameterAction G e
  let : Fintype (SchubertGeometry.deodharIndex G e) := Fintype.ofFinite _
  have hp : parameterCoordinate e x ⟨decreasingJ1⟩ ≠ 0 :=
    coordinate_omitted_nonzero e x ⟨decreasingJ1⟩ (by
      change (1 : Fin 3) ∈ equalSteps (weylCoxeterSystem G.rootBase) e
      rw [decreasing_equal]
      rfl)
  have hr : Set.range (fun j : {j : SchubertGeometry.deodharIndex G e //
        parameterCoordinate e x j ≠ 0} => parameterWeight e j.val) =
      Set.range (fun i : {i : Fin 2 //
        (![parameterCoordinate e x ⟨decreasingJ1⟩,
          parameterCoordinate e x ⟨decreasingJ2⟩] : Fin 2 → K) i ≠ 0} =>
        fun k : ULift.{u} (Fin 3) => decreasingWeights i.val k.down) := by
    ext v
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      rcases decreasing_index_cases j with rfl | rfl
      · exact ⟨⟨0, hj⟩, decreasing_weight1.symm⟩
      · exact ⟨⟨1, hj⟩, decreasing_weight2.symm⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      fin_cases i
      · exact ⟨⟨⟨decreasingJ1⟩, hi⟩, decreasing_weight1⟩
      · exact ⟨⟨⟨decreasingJ2⟩, hi⟩, decreasing_weight2⟩
  have ht := GroupActions.torus_orbitNatDim_of_immersion G
    (SchubertGeometry.deodharParameters G e) (SchubertGeometry.deodharParameterInclusion G e)
    (fun j => (SchubertOrbits.subwordCharacter G e j.down).toAdd) x
    (fun t j => SchubertOrbits.deodharParameter_smul G e t x j)
  change GroupActions.orbitNatDim (GroupActions.torusVariety G)
    (SchubertGeometry.deodharParameters G e) x = Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun j : {j : SchubertGeometry.deodharIndex G e //
        parameterCoordinate e x j ≠ 0} => parameterWeight e j.val))) at ht
  rw [hr] at ht
  exact ht.trans (decreasing_lifted_active_rank _ _ hp)

/-- Every 111 parameter orbit has dimension two. -/
theorem positive_parameter_rank
    (x : (SchubertGeometry.deodharParameters (GLn.groupData K 3) positiveExpression).points) :
    let := SchubertOrbits.deodharParameterAction (GLn.groupData K 3) positiveExpression
    GroupActions.orbitNatDim (GroupActions.torusVariety (GLn.groupData K 3))
      (SchubertGeometry.deodharParameters (GLn.groupData K 3) positiveExpression) x = 2 := by
  classical
  let G := GLn.groupData K 3
  let e := positiveExpression (K := K)
  let := SchubertOrbits.deodharParameterAction G e
  let : Fintype (SchubertGeometry.deodharIndex G e) := Fintype.ofFinite _
  have hn (j : SchubertGeometry.deodharIndex G e) : parameterCoordinate e x j ≠ 0 :=
    coordinate_omitted_nonzero e x j
      ((Set.ext_iff.mp (positive_equal (K := K)) j.down.val).mpr trivial)
  have hr : Set.range (fun j : {j : SchubertGeometry.deodharIndex G e //
        parameterCoordinate e x j ≠ 0} => parameterWeight e j.val) =
      Set.range (fun i : Fin 3 =>
        fun k : ULift.{u} (Fin 3) => positiveWeights i k.down) := by
    ext v
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      have he := positive_index_eq j
      exact ⟨j.down.val, (positive_weight _).symm.trans
        (congrArg (parameterWeight e) he).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨⟨positiveJ i⟩, hn _⟩, positive_weight i⟩
  have ht := GroupActions.torus_orbitNatDim_of_immersion G
    (SchubertGeometry.deodharParameters G e) (SchubertGeometry.deodharParameterInclusion G e)
    (fun j => (SchubertOrbits.subwordCharacter G e j.down).toAdd) x
    (fun t j => SchubertOrbits.deodharParameter_smul G e t x j)
  change GroupActions.orbitNatDim (GroupActions.torusVariety G)
    (SchubertGeometry.deodharParameters G e) x = Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun j : {j : SchubertGeometry.deodharIndex G e //
        parameterCoordinate e x j ≠ 0} => parameterWeight e j.val))) at ht
  rw [hr] at ht
  exact ht.trans positive_lifted_rank

/-- The characters of s₁1s₁ span a two-dimensional real space. -/
theorem decreasing_character_rank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (parameterWeight (K := K) decreasingExpression))) = 2 := by
  have hr : Set.range (parameterWeight (K := K) decreasingExpression) =
      Set.range (fun i : Fin 2 =>
        fun k : ULift.{u} (Fin 3) => decreasingWeights i k.down) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      rcases decreasing_index_cases j with rfl | rfl
      · exact ⟨0, decreasing_weight1.symm⟩
      · exact ⟨1, decreasing_weight2.symm⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨⟨decreasingJ1⟩, decreasing_weight1⟩
      · exact ⟨⟨decreasingJ2⟩, decreasing_weight2⟩
  rw [hr]
  exact decreasing_lifted_rank

/-- The characters of 111 span a two-dimensional real space. -/
theorem positive_character_rank :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (parameterWeight (K := K) positiveExpression))) = 2 := by
  have hr : Set.range (parameterWeight (K := K) positiveExpression) =
      Set.range (fun i : Fin 3 =>
        fun k : ULift.{u} (Fin 3) => positiveWeights i k.down) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.down.val, (positive_weight _).symm.trans
        (congrArg (parameterWeight positiveExpression) (positive_index_eq j)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨positiveJ i⟩, positive_weight i⟩
  rw [hr]
  exact positive_lifted_rank

end SchubertOrbits.GL3
