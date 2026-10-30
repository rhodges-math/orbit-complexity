import OrbitComplexity.GroupActions.Tori.SupportMaps
import OrbitComplexity.GroupActions.Tori.ProjectiveWeights
import OrbitComplexity.GroupActions.MomentMaps.Basic
import Mathlib.LinearAlgebra.AffineSpace.Dimension
import Mathlib.Analysis.Complex.Polynomial.Basic
import OrbitComplexity.GroupActions.Representations.ProjectiveAction
import OrbitComplexity.GroupActions.Varieties.AffineCoordinates
import OrbitComplexity.GroupActions.Varieties.AffineImages
import OrbitComplexity.GroupActions.Varieties.ImmersionDimension
import OrbitComplexity.GroupActions.Actions.Orbits
import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! # Dimensions of diagonal projective orbits

In a chart whose base coordinate is nonzero, a diagonal orbit is parametrized by
monomials with character differences. Its dimension is the real rank of those
differences on the vector's support.

## Main results

* GroupActions.projective_orbit_dim: the supported character-difference rank.
* GroupActions.projective_orbit_polytope_dim: equality with the weight-polytope dimension.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Multiplicative TauCeti WithConv
open scoped TensorProduct
noncomputable section
namespace GroupActions
universe u
variable {K I J : Type u} [Field K] [Fintype I] [DecidableEq I] [Finite J]

omit [Finite J] in
private theorem character_sub
    (g : MonoidAlgebra K (Multiplicative (J →₀ ℤ)) →ₐ[K] K) (a b : J →₀ ℤ) :
    g (MonoidAlgebra.single (ofAdd (a - b)) 1) =
      g (MonoidAlgebra.single (ofAdd a) 1) /
        g (MonoidAlgebra.single (ofAdd b) 1) := by
  apply (eq_div_iff (projective_character_ne_zero g b)).mpr
  rw [← map_mul, MonoidAlgebra.single_mul_single]
  simp

variable [IsAlgClosed K]

private theorem orbit_chart (χ : I → J →₀ ℤ) (v : I → K) (hv : v ≠ 0)
    (i₀ : I) (hi₀ : v i₀ ≠ 0)
    (g : WithConv (MonoidAlgebra K (Multiplicative (J →₀ ℤ)) →ₐ[K] K)) :
    letI : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
      Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun K I)
    affineGroupPointsMulEquiv K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) g •
        projectiveVectorPoint v hv =
      Variety.mapPoints
        (affineMorphism (weightedPolynomialMap
          (fun i : {i : I // i ≠ i₀} => χ i.val - χ i₀)
          (fun i : {i : I // i ≠ i₀} => v i.val / v i₀)) ≫
          projectiveChartMorphism K I i₀)
        (affineGroupPointsMulEquiv K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) g) := by
  let : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
    Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun K I)
  rw [projective_weights_smul χ g v hv]
  rw [@projectiveVectorPoint_chart K I inferInstance inferInstance
    (fun i => v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1)) _ i₀
    (mul_ne_zero hi₀ (projective_character_ne_zero g.ofConv (χ i₀)))]
  rw [Variety.mapPoints_comp]
  apply congrArg (Variety.mapPoints (projectiveChartMorphism K I i₀))
  apply (affineSpaceVarietyPointsEquiv K {i : I // i ≠ i₀}).injective
  funext i
  rw [Equiv.apply_symm_apply]
  have hc := @affineMorphism_coordinate K
    (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) {i : I // i ≠ i₀}
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (weightedPolynomialMap (fun i : {i : I // i ≠ i₀} => χ i.val - χ i₀)
      (fun i : {i : I // i ≠ i₀} => v i.val / v i₀))
    (affineGroupPointsMulEquiv K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) g) i
  refine Eq.trans ?_ hc.symm
  rw [weightedPolynomialMap_X]
  have hg : affineVarietyPointsEquiv K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))
      (affineGroupPointsMulEquiv K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) g) =
      g.ofConv := affinePointsEquiv.symm_apply_apply g.ofConv
  rw [hg]
  change (v i.val * g.ofConv (MonoidAlgebra.single (ofAdd (χ i.val)) 1)) /
      (v i₀ * g.ofConv (MonoidAlgebra.single (ofAdd (χ i₀)) 1)) =
    g.ofConv ((v i.val / v i₀) • MonoidAlgebra.single (ofAdd (χ i.val - χ i₀)) 1)
  rw [map_smul, smul_eq_mul, character_sub]
  rw [mul_div_mul_comm]

private theorem image_dim_immersion {X Y Z : Variety K}
    (f : Z.toOver ⟶ X.toOver) (g : X.toOver ⟶ Y.toOver) [IsImmersion g.left]
    (hI : IsIrreducible (Set.range (f.left : Z.scheme → X.scheme))) :
    Y.subsetDim (Set.range (Variety.mapPoints (f ≫ g))) =
      X.subsetDim (Set.range (Variety.mapPoints f)) := by
  rw [Variety.subsetDim, Variety.subsetDim, Variety.pointClosure_range,
    Variety.pointClosure_range]
  change topologicalKrullDim (closure (Set.range
    ((g.left : X.scheme → Y.scheme) ∘ (f.left : Z.scheme → X.scheme)))) = _
  rw [Set.range_comp, ← closure_image_closure g.left.continuous]
  have h := Variety.dim_closure_image_immersion g
    (closure (Set.range (f.left : Z.scheme → X.scheme)))
    isClosed_closure.isLocallyClosed hI.closure
  exact h.trans (congrArg (fun S : Set X.scheme => topologicalKrullDim S) closure_closure)

omit [Fintype I] [Finite J] [IsAlgClosed K] in
private theorem chart_span (χ : I → J →₀ ℤ) (v : I → K) (i₀ : I) (hi₀ : v i₀ ≠ 0) :
    Submodule.span ℝ (Set.range (fun
      (i : {i : {i : I // i ≠ i₀} // v i.val / v i₀ ≠ 0}) j =>
        ((χ i.val.val - χ i₀) j : ℝ))) =
    Submodule.span ℝ (Set.range (fun (i : {i : I // v i ≠ 0}) j =>
      ((χ i.val - χ i₀) j : ℝ))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨⟨i.val.val, (div_ne_zero_iff.mp i.property).1⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    by_cases h : i = i₀
    · subst i
      change (fun j => ((χ i₀ - χ i₀) j : ℝ)) ∈ _
      have hz : (fun j => ((χ i₀ - χ i₀) j : ℝ)) = (0 : J → ℝ) := by
        funext j
        simp
      rw [hz]
      exact zero_mem _
    · exact Submodule.subset_span ⟨⟨⟨i, h⟩, div_ne_zero hi hi₀⟩, rfl⟩

/-- A projective diagonal orbit has the rank of the supported character differences. -/
theorem projective_orbit_dim (χ : I → J →₀ ℤ) (v : I → K) (hv : v ≠ 0)
    (i₀ : I) (hi₀ : v i₀ ≠ 0) :
    letI : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
      Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun K I)
    orbitDim (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))))
      (projectiveVariety K I) (projectiveVectorPoint v hv) =
      (Module.finrank ℝ (Submodule.span ℝ (Set.range
        (fun (i : {i : I // v i ≠ 0}) j => ((χ i.val - χ i₀) j : ℝ)))) :
        WithBot ℕ∞) := by
  let : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
    Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun K I)
  let f := affineMorphism (weightedPolynomialMap
    (fun i : {i : I // i ≠ i₀} => χ i.val - χ i₀)
    (fun i : {i : I // i ≠ i₀} => v i.val / v i₀))
  have hI : IsIrreducible (Set.range (f.left :
      (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))).scheme →
        (affineSpaceVariety K {i : I // i ≠ i₀}).scheme)) := by
    have : IrreducibleSpace
        (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))).scheme := by
      change IrreducibleSpace (Spec (CommRingCat.of
        (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))))
      infer_instance
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ
        (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))).scheme).image
        (f.left : (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))).scheme →
          (affineSpaceVariety K {i : I // i ≠ i₀}).scheme)
        f.left.continuous.continuousOn
  have ho : MulAction.orbit
      (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))).points
      (projectiveVectorPoint v hv) =
      Set.range (Variety.mapPoints (f ≫ projectiveChartMorphism K I i₀)) := by
    ext y
    rw [MulAction.mem_orbit_iff, Set.mem_range]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨g, rfl⟩ := (affineGroupPointsMulEquiv K
        (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))).surjective t
      exact ⟨_, (orbit_chart χ v hv i₀ hi₀ g).symm.trans ht⟩
    · rintro ⟨t, ht⟩
      obtain ⟨g, rfl⟩ := (affineGroupPointsMulEquiv K
        (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))).surjective t
      exact ⟨_, (orbit_chart χ v hv i₀ hi₀ g).trans ht⟩
  unfold orbitDim
  rw [ho, image_dim_immersion f (projectiveChartMorphism K I i₀) hI]
  rw [affineMorphism_image_dim, ringKrullDim_weighted_real, chart_span χ v i₀ hi₀]

private theorem polytope_finDim {I E : Type*} [AddCommGroup E] [Module ℝ E]
    (weight : I → E) (v : I → ℂ) (hv : v ≠ 0) (i₀ : I) (hi₀ : v i₀ ≠ 0) :
    (affineSpan ℝ (weightPolytope weight (Projectivization.mk ℂ v hv))).finDim =
      (Module.finrank ℝ (Submodule.span ℝ (Set.range
        (fun i : {i : I // v i ≠ 0} => weight i.val - weight i₀))) : WithBot ℕ) := by
  have hset : weight '' Function.support v =
      Set.range (fun i : {i : I // v i ≠ 0} => weight i.val) := by
    ext y
    simp
  have hne : affineSpan ℝ
      (Set.range (fun i : {i : I // v i ≠ 0} => weight i.val)) ≠ ⊥ :=
    ((bot_lt_affineSpan ℝ).mpr ⟨_, Set.mem_range_self ⟨i₀, hi₀⟩⟩).ne'
  rw [weightPolytope_mk, affineSpan_convexHull, hset,
    AffineSubspace.finDim_eq_finrank hne, direction_affineSpan,
    vectorSpan_range_eq_span_range_vsub_right ℝ _ ⟨i₀, hi₀⟩]
  rfl


private theorem real_character_sub {J : Type*} (a b : J →₀ ℤ) :
    (fun j => (a j : ℝ)) - (fun j => (b j : ℝ)) =
      (fun j => ((a - b) j : ℝ)) := by
  funext j
  simp only [Pi.sub_apply, Finsupp.sub_apply, Int.cast_sub]

/-- The supported weight polytope and the diagonal projective orbit have the same dimension. -/
theorem projective_orbit_polytope_dim {I J : Type} [Fintype I] [DecidableEq I] [Finite J]
    (χ : I → J →₀ ℤ) (v : I → ℂ) (hv : v ≠ 0) (i₀ : I) (hi₀ : v i₀ ≠ 0) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
      I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    let n := Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun (i : {i : I // v i ≠ 0}) j => ((χ i.val - χ i₀) j : ℝ))))
    orbitDim (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
        (projectiveVariety ℂ I) (projectiveVectorPoint v hv) = (n : WithBot ℕ∞) ∧
      (affineSpan ℝ (weightPolytope (fun i j => (χ i j : ℝ))
        (Projectivization.mk ℂ v hv))).finDim = (n : WithBot ℕ) := by
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
    I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  constructor
  · exact @projective_orbit_dim ℂ I J inferInstance inferInstance inferInstance
      inferInstance inferInstance χ v hv i₀ hi₀
  · refine (polytope_finDim (fun i j => (χ i j : ℝ)) v hv i₀ hi₀).trans ?_
    apply congrArg (fun S : Submodule ℝ (J → ℝ) =>
      (Module.finrank ℝ S : WithBot ℕ))
    apply congrArg (Submodule.span ℝ)
    apply congrArg Set.range
    funext i
    exact real_character_sub (χ i.val) (χ i₀)

end GroupActions
