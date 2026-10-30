import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Rat
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Field.Rat
import Batteries.Tactic.Lint

/-! # Rational points in linear kernels

Rational solutions are dense among real solutions of rational homogeneous equations.
Consequently one can preserve zeros and strict signs, then clear all denominators
with one positive integer.
-/

open Matrix Set

noncomputable section

namespace GroupActions

universe u v

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

private theorem matrix_generalized_inverse (A : Matrix J I ℚ) :
    ∃ G : Matrix I J ℚ, A * G * A = A := by
  classical
  let f := A.toLin'
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨h, hh⟩ := g.exists_extend
  have hf : f.comp (h.comp f) = f := by
    apply LinearMap.ext
    intro v
    have hh' := LinearMap.congr_fun hh (f.rangeRestrict v)
    have hg' := congrArg Subtype.val (LinearMap.congr_fun hg (f.rangeRestrict v))
    change f (h (f v)) = f v
    change h (f v) = g (f.rangeRestrict v) at hh'
    rw [hh']
    exact hg'
  refine ⟨h.toMatrix', ?_⟩
  have hm := congrArg LinearMap.toMatrix' hf
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.mul_assoc, f] using hm

/-- Every open neighborhood of a real solution of rational homogeneous equations contains
an exact rational solution. -/
theorem exists_rat_kernel_open (A : Matrix J I ℚ) (x : I → ℝ)
    (hx : A.map (algebraMap ℚ ℝ) *ᵥ x = 0) (U : Set (I → ℝ))
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ q : I → ℚ, A *ᵥ q = 0 ∧ (fun i ↦ (q i : ℝ)) ∈ U := by
  classical
  obtain ⟨G, hG⟩ := matrix_generalized_inverse A
  let P : Matrix I I ℚ := 1 - G * A
  have hP : A * P = 0 := by
    dsimp only [P]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hG, sub_self]
  let PR : Matrix I I ℝ := P.map (algebraMap ℚ ℝ)
  have hPx : PR *ᵥ x = x := by
    dsimp only [PR, P]
    rw [Matrix.map_sub, Matrix.map_one, Matrix.map_mul, Matrix.sub_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]
    all_goals simp
  have hcont : Continuous (fun y : I → ℝ ↦ PR *ᵥ y) := by
    apply continuous_pi
    intro i
    exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul (continuous_apply j)
  have hd : DenseRange (fun q : I → ℚ ↦ fun i ↦ (q i : ℝ)) :=
    DenseRange.piMap (fun _ ↦ Rat.denseRange_cast)
  obtain ⟨y, hyU, q, rfl⟩ :=
    (mem_closure_iff.mp (hd x)) _ (hU.preimage hcont) (show PR *ᵥ x ∈ U from hPx.symm ▸ hxU)
  refine ⟨P *ᵥ q, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, hP, Matrix.zero_mulVec]
  · have he : (fun i ↦ ((P *ᵥ q) i : ℝ)) = PR *ᵥ (fun i ↦ (q i : ℝ)) := by
      ext i
      exact RingHom.map_mulVec (algebraMap ℚ ℝ) P q i
    rw [he]
    exact hyU

/-- A rational homogeneous system has a rational solution with the same zero coordinates
and the same strict signs as any given real solution. -/
theorem exists_rat_kernel_sign (A : Matrix J I ℚ) (x : I → ℝ)
    (hx : A.map (algebraMap ℚ ℝ) *ᵥ x = 0) :
    ∃ q : I → ℚ, A *ᵥ q = 0 ∧ (∀ i, x i = 0 → q i = 0) ∧
      (∀ i, 0 < x i → 0 < q i) ∧ (∀ i, x i < 0 → q i < 0) := by
  classical
  let B : Matrix (J ⊕ I) I ℚ := fun j i ↦ match j with
    | Sum.inl j => A j i
    | Sum.inr k => if x k = 0 ∧ i = k then 1 else 0
  have hxB : B.map (algebraMap ℚ ℝ) *ᵥ x = 0 := by
    ext j
    cases j with
    | inl j => exact congrFun hx j
    | inr k =>
      change (∑ i, (algebraMap ℚ ℝ) (if x k = 0 ∧ i = k then (1 : ℚ) else 0) * x i) = 0
      by_cases hk : x k = 0
      · simp [hk]
      · simp [hk]
  let U : Set (I → ℝ) :=
    (⋂ i ∈ Finset.univ.filter (fun i ↦ 0 < x i), {y | 0 < y i}) ∩
      (⋂ i ∈ Finset.univ.filter (fun i ↦ x i < 0), {y | y i < 0})
  have hU : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_biInter_finset fun i _ ↦ isOpen_lt continuous_const (continuous_apply i)
    · exact isOpen_biInter_finset fun i _ ↦ isOpen_lt (continuous_apply i) continuous_const
  have hxU : x ∈ U := by simp [U]
  obtain ⟨q, hq, hqU⟩ := exists_rat_kernel_open B x hxB U hU hxU
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · ext j
    exact congrFun hq (Sum.inl j)
  · intro i hi
    have hz := congrFun hq (Sum.inr i)
    simpa [Matrix.mulVec, dotProduct, B, hi] using hz
  · intro i hi
    have ht : (0 : ℝ) < q i := (Set.mem_iInter₂.mp hqU.1) i (by simp [hi])
    exact_mod_cast ht
  · intro i hi
    have ht : (q i : ℝ) < 0 := (Set.mem_iInter₂.mp hqU.2) i (by simp [hi])
    exact_mod_cast ht

/-- A finite family of rationals has a common positive integer denominator. -/
theorem exists_pos_integer_multiple (q : I → ℚ) :
    ∃ c : ℤ, 0 < c ∧ ∃ n : I → ℤ, ∀ i, (n i : ℚ) = (c : ℚ) * q i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) q
  choose n hn using hb
  refine ⟨(b : ℤ) * b, mul_self_pos.mpr (nonZeroDivisors.coe_ne_zero b),
    fun i ↦ (b : ℤ) * n i, ?_⟩
  intro i
  have hi : (n i : ℚ) = (b : ℚ) * q i := by
    simpa only [Algebra.smul_def, eq_intCast] using hn i
  push_cast
  rw [hi, mul_assoc]

end GroupActions
