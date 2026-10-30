import OrbitComplexity.Paper.Deodhar.GL3Flags
import OrbitComplexity.Paper.Deodhar.GL3ParameterRanks
import OrbitComplexity.Paper.Deodhar.GL3RootProducts
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

/-! # Torus orbits of rank-three matrix flags -/

open ReductiveGroups TauCeti TauCeti.GeneralLinear Module Submodule
open ReductiveGroups.GLn
open CategoryTheory AlgebraicGeometry GroupActions GroupActions.Variety
open SchubertGeometry BruhatIntervals
open scoped Classical

noncomputable section
namespace SchubertOrbits.GL3
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

section GenericParameters
variable (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private theorem parameterPoint_exists (p : Fin word.length → K)
    (hp : ∀ j ∈ equalSteps (weylCoxeterSystem G.rootBase) expression, p j ≠ 0) :
    ∃ x : (deodharParameters G expression).points,
      ∀ j : deodharIndex G expression,
        affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
          (mapPoints (X := deodharParameters G expression)
      (Y := affineSpaceVariety K (deodharIndex G expression))
      (deodharParameterInclusion G expression) x) j = p j.down.val := by
  let a : deodharIndex G expression → K := fun j => p j.down.val
  let q := (affineSpaceVarietyPointsEquiv K (deodharIndex G expression)).symm a
  have hq : q ∈ Set.range (mapPoints (X := deodharParameters G expression)
      (Y := affineSpaceVariety K (deodharIndex G expression))
      (deodharParameterInclusion G expression)) := by
    apply (deodharParameter_points G expression).symm.subset
    intro j hj
    change affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
      ((affineSpaceVarietyPointsEquiv K (deodharIndex G expression)).symm a) j ≠ 0
    rw [Equiv.apply_symm_apply]
    exact hp j.down.val hj
  obtain ⟨x, hx⟩ := hq
  refine ⟨x, fun j => ?_⟩
  exact (congrArg (fun z : (affineSpaceVariety K (deodharIndex G expression)).points =>
    affineSpaceVarietyPointsEquiv K (deodharIndex G expression) z j) hx).trans
      (congrFun (Equiv.apply_symm_apply
        (affineSpaceVarietyPointsEquiv K (deodharIndex G expression)) a) j)

private theorem prefix_at_parameterPoint (p : Fin word.length → K)
    (x : (deodharParameters G expression).points)
    (hx : ∀ j : deodharIndex G expression,
      affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
        (mapPoints (X := deodharParameters G expression)
      (Y := affineSpaceVariety K (deodharIndex G expression))
      (deodharParameterInclusion G expression) x) j = p j.down.val)
    (n : ℕ) :
    mapPoints (deodharPrefixMorphism G expression n) x =
      flagVarietyPointsEquiv G (flagProjection G (deodharPrefix G expression p n)) := by
  have hc : (fun j => affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
      (mapPoints (X := deodharParameters G expression)
      (Y := affineSpaceVariety K (deodharIndex G expression))
      (deodharParameterInclusion G expression) x) ⟨j⟩) =
        (fun j => p j.val) := funext (fun j => hx ⟨j⟩)
  have hm := deodharPrefixMorphism_points G expression n x
  rw [hc, ← deodharPrefix_rootProduct] at hm
  exact hm

private theorem parameter_flag_orbit
    (hred : (weylCoxeterSystem G.rootBase).IsReduced word)
    (hd : IsDistinguished (weylCoxeterSystem G.rootBase) expression)
    (x : (deodharParameters G expression).points) :
    let := SchubertOrbits.deodharParameterAction G expression
    orbitNatDim (torusVariety G) (deodharParameters G expression) x =
      orbitNatDim (torusVariety G) (flagVariety G)
        (mapPoints (deodharPrefixMorphism G expression word.length) x) := by
  let := SchubertOrbits.deodharParameterAction G expression
  have : IsModHom (torusVariety G).toOver
      (deodharComponentIso G expression hred hd).hom :=
    (SchubertOrbits.deodharComponent_weights G expression hred hd).1
  let y := mapPoints (X := deodharParameters G expression)
    (Y := deodharComponent G expression hred)
    (deodharComponentIso G expression hred hd).hom x
  have ho := orbitNatDim_iso (torusVariety G) (X := deodharParameters G expression)
    (Y := deodharComponent G expression hred) (deodharComponentIso G expression hred hd) x
  have hf := SchubertOrbits.deodhar_orbitNatDim G expression hred y
  have hc := congrArg (fun f => mapPoints (X := deodharParameters G expression)
    (Y := flagVariety G) f x) (deodharComponentIso_flag G expression hred hd)
  have hm := mapPoints_comp (X := deodharParameters G expression)
    (Y := deodharComponent G expression hred) (Z := flagVariety G)
    (deodharComponentIso G expression hred hd).hom (deodharInclusion G expression hred) x
  have he : mapPoints (X := deodharComponent G expression hred) (Y := flagVariety G)
      (deodharInclusion G expression hred) y =
        mapPoints (deodharPrefixMorphism G expression word.length) x := hm.symm.trans hc
  exact ho.symm.trans (hf.symm.trans
    (congrArg (orbitNatDim (torusVariety G) (flagVariety G)) he))

end GenericParameters

attribute [local instance] matrixWord_neZero

private theorem parameterFlag_matrix
    (expression : Subexpression (matrixWord (K := K)))
    (p : Fin (matrixWord (K := K)).length → K)
    (x : (deodharParameters (GLn.groupData K 3) expression).points)
    (hx : ∀ j : deodharIndex (GLn.groupData K 3) expression,
      affineSpaceVarietyPointsEquiv K (deodharIndex (GLn.groupData K 3) expression)
        (mapPoints (X := deodharParameters (GLn.groupData K 3) expression)
          (Y := affineSpaceVariety K (deodharIndex (GLn.groupData K 3) expression))
          (deodharParameterInclusion (GLn.groupData K 3) expression) x) j = p j.down.val)
    (A : GL (Fin 3) K)
    (hA : (matrixPoints (deodharPrefix (GLn.groupData K 3) expression p 3) :
      Matrix (Fin 3) (Fin 3) K) = A) :
    mapPoints (X := deodharParameters (GLn.groupData K 3) expression)
      (Y := flagVariety (GLn.groupData K 3))
      (deodharPrefixMorphism (GLn.groupData K 3) expression 3) x = schemeMatrixFlag A := by
  have hg : matrixPoints (deodharPrefix (GLn.groupData K 3) expression p 3) = A :=
    Units.ext hA
  have he : deodharPrefix (GLn.groupData K 3) expression p 3 =
      (matrixPoints (K := K)).symm A := by
    apply (matrixPoints (K := K)).injective
    exact hg.trans ((matrixPoints (K := K)).apply_symm_apply A).symm
  have hf := prefix_at_parameterPoint (GLn.groupData K 3) expression p x hx 3
  exact hf.trans (congrArg (fun g : (GLn.groupData K 3).points =>
    flagVarietyPointsEquiv (GLn.groupData K 3) (flagProjection (GLn.groupData K 3) g)) he)

/-- The s₁1s₁ flag orbit has dimension one at zero last parameter and two otherwise. -/
theorem decreasing_matrix_flag_rank (p m : K) (hp : p ≠ 0) :
    orbitNatDim (torusVariety (GLn.groupData K 3)) (flagVariety (GLn.groupData K 3))
      (schemeMatrixFlag (decreasingGL p m)) = if m = 0 then 1 else 2 := by
  obtain ⟨a, b, ha0, hb0, hmatrix⟩ := decreasing_prefix_matrix (K := K)
  let q : Fin (matrixWord (K := K)).length → K := ![0, -p / a, -m / b]
  have hq : ∀ j ∈ equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      decreasingExpression, q j ≠ 0 := by
    intro j hj
    rw [decreasing_equal, Set.mem_singleton_iff] at hj
    subst j
    exact div_ne_zero (neg_ne_zero.mpr hp) ha0
  obtain ⟨x, hx⟩ := parameterPoint_exists (GLn.groupData K 3) decreasingExpression q hq
  have hm : (matrixPoints (deodharPrefix (GLn.groupData K 3) decreasingExpression q 3) :
      Matrix (Fin 3) (Fin 3) K) = decreasingGL p m := by
    rw [hmatrix]
    change decreasingMatrix (-((-p / a) * a)) (-((-m / b) * b)) = decreasingMatrix p m
    rw [div_mul_cancel₀ _ ha0, div_mul_cancel₀ _ hb0, neg_neg, neg_neg]
  have hf := parameterFlag_matrix decreasingExpression q x hx (decreasingGL p m) hm
  have ho := parameter_flag_orbit (GLn.groupData K 3) decreasingExpression
    matrixWord_reduced decreasing_distinguished x
  have hr := decreasing_parameter_rank x
  have hx2 := hx ⟨decreasingJ2⟩
  change parameterCoordinate decreasingExpression x ⟨decreasingJ2⟩ = -m / b at hx2
  have hc : parameterCoordinate decreasingExpression x ⟨decreasingJ2⟩ = 0 ↔ m = 0 := by
    rw [hx2]
    simp only [div_eq_zero_iff, neg_eq_zero, hb0, or_false]
  simp only [hc] at hr
  have he := congrArg (orbitNatDim (torusVariety (GLn.groupData K 3))
    (flagVariety (GLn.groupData K 3))) hf
  exact he.symm.trans (ho.symm.trans hr)

/-- Every admissible 111 matrix flag has torus orbit dimension two. -/
theorem positive_matrix_flag_rank (a b c : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    orbitNatDim (torusVariety (GLn.groupData K 3)) (flagVariety (GLn.groupData K 3))
      (schemeMatrixFlag (positiveGL a b c)) = 2 := by
  obtain ⟨d, hd0, hmatrix⟩ := positive_prefix_matrix (K := K)
  let q : Fin (matrixWord (K := K)).length → K := ![a / d 0, b / d 1, c / d 2]
  have hq : ∀ j ∈ equalSteps (weylCoxeterSystem (GLn.groupData K 3).rootBase)
      positiveExpression, q j ≠ 0 := by
    intro j _
    fin_cases j
    · exact div_ne_zero ha (hd0 0)
    · exact div_ne_zero hb (hd0 1)
    · exact div_ne_zero hc (hd0 2)
  obtain ⟨x, hx⟩ := parameterPoint_exists (GLn.groupData K 3) positiveExpression q hq
  have hm : (matrixPoints (deodharPrefix (GLn.groupData K 3) positiveExpression q 3) :
      Matrix (Fin 3) (Fin 3) K) = positiveGL a b c := by
    rw [hmatrix]
    change positiveMatrix ((a / d 0) * d 0) ((b / d 1) * d 1)
      ((c / d 2) * d 2) = positiveMatrix a b c
    rw [div_mul_cancel₀ _ (hd0 0), div_mul_cancel₀ _ (hd0 1), div_mul_cancel₀ _ (hd0 2)]
  have hf := parameterFlag_matrix positiveExpression q x hx (positiveGL a b c) hm
  have ho := parameter_flag_orbit (GLn.groupData K 3) positiveExpression
    matrixWord_reduced positive_distinguished x
  have hr := positive_parameter_rank x
  have he := congrArg (orbitNatDim (torusVariety (GLn.groupData K 3))
    (flagVariety (GLn.groupData K 3))) hf
  exact he.symm.trans (ho.symm.trans hr)

end SchubertOrbits.GL3
