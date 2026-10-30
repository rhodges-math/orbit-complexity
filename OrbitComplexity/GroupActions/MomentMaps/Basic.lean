import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Batteries.Tactic.Lint

/-! # Moment maps of finite complex weight spaces

Norm-square centers of mass are independent of the nonzero representative of
an analytic projective point. Their values belong to the convex hull of the
weights whose coordinates are nonzero.

## References

* E. Tsukerman and L. Williams, *Bruhat interval polytopes*, Adv. Math. 285 (2015), 766–810,
  Definition 6.18.
-/

namespace GroupActions

noncomputable section

/-- Projectivization carries the quotient topology of its nonzero vectors. -/
instance projectivizationTopology {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [TopologicalSpace V] : TopologicalSpace (Projectivization K V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid K V)))

variable {I E : Type*} [Fintype I] [AddCommGroup E] [Module ℝ E]

/-- The total norm-square of a nonzero finite complex vector is positive. -/
theorem sum_normSq_pos (z : I → ℂ) (hz : z ≠ 0) :
    0 < ∑ i, Complex.normSq (z i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  apply Finset.sum_pos'
  · intro j _
    exact Complex.normSq_nonneg _
  · exact ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

/-- A common nonzero complex scalar does not change the norm-square center of mass. -/
theorem centerMass_normSq_smul (weight : I → E) (z : I → ℂ) (a : ℂ) (ha : a ≠ 0) :
    Finset.univ.centerMass (fun i => Complex.normSq ((a • z) i)) weight =
      Finset.univ.centerMass (fun i => Complex.normSq (z i)) weight := by
  have hs : (fun i => Complex.normSq ((a • z) i)) =
      Complex.normSq a • (fun i => Complex.normSq (z i)) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [hs]
  exact Finset.centerMass_smul_left (t := Finset.univ) (w := fun i => Complex.normSq (z i))
    (z := weight) (c := Complex.normSq a) (Complex.normSq_pos.mpr ha).ne'

/-- The moment map is the norm-square center of mass of a projective representative. -/
def momentMap (weight : I → E) : Projectivization ℂ (I → ℂ) → E :=
  Projectivization.lift
    (fun z => Finset.univ.centerMass (fun i => Complex.normSq (z.val i)) weight)
    (by
      intro z z' a h
      have ha : a ≠ 0 := by
        intro hzero
        apply z.property
        rw [h, hzero, zero_smul]
      change Finset.univ.centerMass (fun i => Complex.normSq (z.val i)) weight = _
      rw [h]
      exact centerMass_normSq_smul weight z'.val a ha)

/-- The moment map has the norm-square formula on every nonzero representative. -/
theorem momentMap_mk (weight : I → E) (z : I → ℂ) (hz : z ≠ 0) :
    momentMap weight (Projectivization.mk ℂ z hz) =
      Finset.univ.centerMass (fun i => Complex.normSq (z i)) weight := rfl

omit [Fintype I] in
/-- The weight polytope is the convex hull of the supported projective weights. -/
def weightPolytope (weight : I → E) : Projectivization ℂ (I → ℂ) → Set E :=
  Projectivization.lift (fun z => convexHull ℝ (weight '' Function.support z.val))
    (by
      intro z z' a h
      have ha : a ≠ 0 := by
        intro hzero
        apply z.property
        rw [h, hzero, zero_smul]
      change convexHull ℝ (weight '' Function.support z.val) = _
      rw [h, Function.support_const_smul_of_ne_zero a z'.val ha])

omit [Fintype I] in
/-- Supported coordinates compute the weight polytope of a projective point. -/
theorem weightPolytope_mk (weight : I → E) (z : I → ℂ) (hz : z ≠ 0) :
    weightPolytope weight (Projectivization.mk ℂ z hz) =
      convexHull ℝ (weight '' Function.support z) := rfl

/-- Every projective moment value belongs to its supported weight polytope. -/
theorem momentMap_mem_weightPolytope (weight : I → E)
    (p : Projectivization ℂ (I → ℂ)) : momentMap weight p ∈ weightPolytope weight p := by
  classical
  refine Projectivization.ind ?_ p
  intro z hz
  rw [momentMap_mk, weightPolytope_mk, ← Finset.centerMass_filter_ne_zero]
  apply Finset.centerMass_mem_convexHull
  · intro i _
    exact Complex.normSq_nonneg _
  · simpa only [Finset.sum_filter_ne_zero] using sum_normSq_pos z hz
  · intro i hi
    refine Set.mem_image_of_mem weight ?_
    exact Complex.normSq_eq_zero.not.mp (Finset.mem_filter.mp hi).2


/-- The moment map is continuous for the analytic quotient topology on projective space. -/
theorem momentMap_continuous [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] (weight : I → E) : Continuous (momentMap weight) := by
  change Continuous (Quotient.lift _ _)
  apply Continuous.quotient_lift
  have hcoord (i : I) : Continuous
      (fun z : {z : I → ℂ // z ≠ 0} => Complex.normSq (z.val i)) :=
    Complex.continuous_normSq.comp ((continuous_apply i).comp continuous_subtype_val)
  have hden : Continuous (fun z : {z : I → ℂ // z ≠ 0} =>
      ∑ i, Complex.normSq (z.val i)) :=
    continuous_finsetSum _ (fun i _ => hcoord i)
  have hnum : Continuous (fun z : {z : I → ℂ // z ≠ 0} =>
      ∑ i, Complex.normSq (z.val i) • weight i) :=
    continuous_finsetSum _ (fun i _ => (hcoord i).smul continuous_const)
  refine ((hden.inv₀ (fun z => (sum_normSq_pos z.val z.property).ne')).smul hnum).congr ?_
  intro z
  rfl

/-- Definition 6.18 of Tsukerman–Williams: for finite weight coordinates, the moment map sends the
line of a nonzero vector `z` to the average of the weights weighted by `|z_i|²`. The total weight
is positive, the average does not depend on the nonzero representative, it lies in the convex
hull of the weights of the support of `z`, and the moment map is continuous. -/
theorem momentMap_definition [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] (weight : I → E) :
    (∀ (z : I → ℂ) (hz : z ≠ 0), 0 < ∑ i, Complex.normSq (z i) ∧
      momentMap weight (Projectivization.mk ℂ z hz) =
        Finset.univ.centerMass (fun i => Complex.normSq (z i)) weight ∧
      weightPolytope weight (Projectivization.mk ℂ z hz) =
        convexHull ℝ (weight '' Function.support z)) ∧
    (∀ (z : I → ℂ) (a : ℂ), a ≠ 0 →
      Finset.univ.centerMass (fun i => Complex.normSq ((a • z) i)) weight =
        Finset.univ.centerMass (fun i => Complex.normSq (z i)) weight) ∧
    (∀ p, momentMap weight p ∈ weightPolytope weight p) ∧
    Continuous (momentMap weight) :=
  ⟨fun z hz => ⟨sum_normSq_pos z hz, momentMap_mk weight z hz, weightPolytope_mk weight z hz⟩,
    fun z a ha => centerMass_normSq_smul weight z a ha,
    momentMap_mem_weightPolytope weight, momentMap_continuous weight⟩

end

end GroupActions
