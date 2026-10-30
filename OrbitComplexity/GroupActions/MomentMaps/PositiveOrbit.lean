import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.LocallyConvex.Separation
import Batteries.Tactic.Lint

/-! # Positive exponential orbits

Positive exponential weights realize exactly the intrinsic interior of their convex hull.
An interior ball in the affine direction gives a coercive sum. Its minimum has zero derivative,
which yields the prescribed center of mass. The parameter is a continuous real linear functional.
-/

namespace GroupActions

open Filter Set
open scoped BigOperators InnerProductSpace

variable {I E : Type*} [NormedAddCommGroup E]

section Geometry
variable [NormedSpace ℝ E]

/-- Subtracting a point of a relative interior gives an interior origin in the direction. -/
theorem interior_convexHull_vsub (A : AffineSubspace ℝ E) [Nonempty A]
    (w : I → A) (q : A)
    (hq : q ∈ interior (((↑) : A → E) ⁻¹' convexHull ℝ (range (fun i => (w i : E))))) :
    (0 : A.direction) ∈ interior (convexHull ℝ (range (fun i => w i -ᵥ q))) := by
  let f : A.direction →ᵃ[ℝ] E :=
    A.subtype.comp (AffineEquiv.vaddConst ℝ q).toAffineMap
  have hf : Function.Injective f :=
    A.subtype_injective.comp (AffineEquiv.vaddConst ℝ q).injective
  have himage : f '' convexHull ℝ (range (fun i => w i -ᵥ q)) =
      convexHull ℝ (range (fun i => (w i : E))) := by
    rw [f.image_convexHull, ← range_comp]
    congr 2
    funext i
    change (((w i -ᵥ q) +ᵥ q : A) : E) = (w i : E)
    rw [vsub_vadd]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hq)
  apply mem_interior_iff_mem_nhds.mpr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨r, hr, ?_⟩
  intro z hz
  have hzA : z +ᵥ q ∈ Metric.ball q r := by
    simpa only [Metric.mem_ball, dist_eq_norm_vsub, vadd_vsub, sub_zero,
      vsub_eq_sub, Subtype.ext_iff] using hz
  have hzP : f z ∈ convexHull ℝ (range (fun i => (w i : E))) := hball hzA
  rw [← himage] at hzP
  obtain ⟨y, hy, heq⟩ := hzP
  exact hf heq ▸ hy

variable [Fintype I]

private theorem centerMass_sub (w : I → E) (a : I → ℝ) (q : E)
    (ha : ∑ i, a i ≠ 0) :
    Finset.univ.centerMass a (fun i => w i - q) = Finset.univ.centerMass a w - q := by
  rw [Finset.centerMass, Finset.centerMass]
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, smul_smul,
    inv_mul_cancel₀ ha, one_smul]


/-- Positive centers of mass belong to the interior of a full-dimensional convex hull. -/
private theorem centerMass_mem_interior [Nonempty I] (w : I → E) (a : I → ℝ)
    (ha : ∀ i, 0 < a i) (hint : (interior (convexHull ℝ (range w))).Nonempty) :
    Finset.univ.centerMass a w ∈ interior (convexHull ℝ (range w)) := by
  classical
  by_contra hnot
  obtain ⟨f, hf, hle⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull ℝ (range w)) hnot hint
  have htotal : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hfx : f (Finset.univ.centerMass a w) = (∑ i, a i)⁻¹ * ∑ i, a i * f (w i) := by
    simp only [Finset.centerMass, map_smul, map_sum, smul_eq_mul]
  have hsum : ∑ i, a i * (f (Finset.univ.centerMass a w) - f (w i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hfx]
    field_simp [htotal.ne']
    ring
  have hnonneg : ∀ i ∈ Finset.univ,
      0 ≤ a i * (f (Finset.univ.centerMass a w) - f (w i)) := by
    intro i _
    exact mul_nonneg (ha i).le (sub_nonneg.mpr
      (hle _ (subset_convexHull ℝ _ (mem_range_self i))))
  have hpoint : ∀ i, f (w i) = f (Finset.univ.centerMass a w) := by
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (ha i).ne')).symm
  have heq : f.toLinearMap.toAffineMap =
      AffineMap.const ℝ E (f (Finset.univ.centerMass a w)) := by
    apply AffineMap.ext_on (affineSpan_eq_top_of_nonempty_interior hint)
    rintro _ ⟨i, rfl⟩
    exact hpoint i
  apply hf
  ext y
  have hy := congrArg (fun g : E →ᵃ[ℝ] ℝ => g y) heq
  have h0 := congrArg (fun g : E →ᵃ[ℝ] ℝ => g 0) heq
  change f y = f (Finset.univ.centerMass a w) at hy
  change f 0 = f (Finset.univ.centerMass a w) at h0
  change f y = 0
  simpa only [map_zero] using hy.trans h0.symm

/-- A center of mass with strictly positive weights lies in the hull's intrinsic interior. -/
theorem centerMass_mem_intrinsicInterior [Nonempty I] [FiniteDimensional ℝ E]
    (w : I → E) (a : I → ℝ) (ha : ∀ i, 0 < a i) :
    Finset.univ.centerMass a w ∈ intrinsicInterior ℝ (convexHull ℝ (range w)) := by
  classical
  have hne : (convexHull ℝ (range w)).Nonempty :=
    (Set.range_nonempty w).convexHull
  obtain ⟨q, hq⟩ := hne.intrinsicInterior (convex_convexHull ℝ (range w))
  obtain ⟨qA, hqA, rfl⟩ := mem_intrinsicInterior.mp hq
  let A := affineSpan ℝ (convexHull ℝ (range w))
  let : Nonempty A := ⟨qA⟩
  let wA : I → A := fun i =>
    ⟨w i, subset_affineSpan ℝ _ (subset_convexHull ℝ _ (mem_range_self i))⟩
  let f : A.direction →ᵃⁱ[ℝ] E := A.subtypeₐᵢ.comp
    (AffineIsometryEquiv.vaddConst ℝ qA).toAffineIsometry
  have hzero := interior_convexHull_vsub A wA qA hqA
  have hinside := centerMass_mem_interior (fun i => wA i -ᵥ qA) a ha ⟨0, hzero⟩
  have himage : f '' convexHull ℝ (range (fun i => wA i -ᵥ qA)) =
      convexHull ℝ (range w) := by
    rw [← f.coe_toAffineMap, f.toAffineMap.image_convexHull, ← range_comp]
    congr 2
    funext i
    change (((wA i -ᵥ qA) +ᵥ qA : A) : E) = w i
    rw [vsub_vadd]
  have hrelative := mem_image_of_mem f (interior_subset_intrinsicInterior (𝕜 := ℝ) hinside)
  rw [← f.intrinsicInterior_image, himage] at hrelative
  have htotal : ∑ i, a i ≠ 0 :=
    (Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty).ne'
  have hproject : ((Finset.univ.centerMass a (fun i => wA i -ᵥ qA) : A.direction) : E) =
      Finset.univ.centerMass a (fun i => w i - (qA : E)) := by
    simp only [Finset.centerMass, Submodule.coe_smul, Submodule.coe_sum,
      AffineSubspace.coe_vsub, vsub_eq_sub, wA]
  have hbar : f (Finset.univ.centerMass a (fun i => wA i -ᵥ qA)) =
      Finset.univ.centerMass a w := by
    change ((Finset.univ.centerMass a (fun i => wA i -ᵥ qA) : A.direction) : E) +
      (qA : E) = _
    rw [hproject, centerMass_sub w a (qA : E) htotal, sub_add_cancel]
  rwa [hbar] at hrelative


end Geometry

section InnerProduct
variable [InnerProductSpace ℝ E]

/-- An interior ball gives a uniform lower bound for a weight pairing in every direction. -/
theorem exists_pos_inner_ge_norm (w : I → E)
    (hzero : (0 : E) ∈ interior (convexHull ℝ (range w))) :
    ∃ ε > 0, ∀ t : E, ∃ i, ε * ‖t‖ ≤ ⟪w i, t⟫_ℝ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  refine ⟨r / 2, half_pos hr, fun t => ?_⟩
  by_cases ht : t = 0
  · obtain ⟨_, ⟨i, rfl⟩⟩ := convexHull_nonempty_iff.mp ⟨0, interior_subset hzero⟩
    exact ⟨i, by simp [ht]⟩
  have hnorm : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hpoint : (r / 2 / ‖t‖) • t ∈ convexHull ℝ (range w) := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (half_pos hr) hnorm), div_mul_cancel₀ _ hnorm.ne']
    linarith
  have hconvex : ConvexOn ℝ univ (fun x : E => ⟪x, t⟫_ℝ) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    simp only [inner_add_left, real_inner_smul_left, smul_eq_mul, le_refl]
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hconvex.exists_ge_of_mem_convexHull (subset_univ _) hpoint
  refine ⟨i, le_trans ?_ hi⟩
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp [hnorm.ne']
  nlinarith

variable [Fintype I]

/-- A positive exponential sum with an interior origin tends to infinity off compact sets. -/
theorem tendsto_sum_exp_inner_atTop [FiniteDimensional ℝ E]
    (w : I → E) (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (hzero : (0 : E) ∈ interior (convexHull ℝ (range w))) :
    Tendsto (fun t : E => ∑ i, a i * Real.exp (2 * ⟪w i, t⟫_ℝ))
      (cocompact E) atTop := by
  classical
  obtain ⟨ε, hε, hsupp⟩ := exists_pos_inner_ge_norm w hzero
  let : Nonempty I := let ⟨i, _⟩ := hsupp 0; ⟨i⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  have hbound : ∀ t : E, (a j * (2 * ε)) * ‖t‖ ≤
      ∑ i, a i * Real.exp (2 * ⟪w i, t⟫_ℝ) := by
    intro t
    obtain ⟨i, hi⟩ := hsupp t
    calc
      (a j * (2 * ε)) * ‖t‖ = a j * (2 * (ε * ‖t‖)) := by ring
      _ ≤ a i * (2 * (ε * ‖t‖)) :=
        mul_le_mul_of_nonneg_right (hj i (Finset.mem_univ i))
          (mul_nonneg (by norm_num) (mul_nonneg hε.le (norm_nonneg t)))
      _ ≤ a i * (2 * ⟪w i, t⟫_ℝ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (by norm_num)) (ha i).le
      _ ≤ a i * Real.exp (2 * ⟪w i, t⟫_ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (2 * ⟪w i, t⟫_ℝ)])
          (ha i).le
      _ ≤ ∑ k, a k * Real.exp (2 * ⟪w k, t⟫_ℝ) :=
        Finset.single_le_sum (fun k _ => mul_nonneg (ha k).le (Real.exp_pos (2 * ⟪w k, t⟫_ℝ)).le)
          (Finset.mem_univ i)
  exact tendsto_atTop_mono hbound
    (tendsto_norm_cocompact_atTop.const_mul_atTop (mul_pos (ha j) (mul_pos (by norm_num) hε)))

/-- A positive exponential sum with an interior origin attains a global minimum. -/
theorem exists_min_sum_exp_inner [FiniteDimensional ℝ E] (w : I → E) (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (hzero : (0 : E) ∈ interior (convexHull ℝ (range w))) :
    ∃ t : E, ∀ s : E, (∑ i, a i * Real.exp (2 * ⟪w i, t⟫_ℝ)) ≤
      ∑ i, a i * Real.exp (2 * ⟪w i, s⟫_ℝ) := by
  have hcontinuous : Continuous (fun t : E => ∑ i, a i * Real.exp (2 * ⟪w i, t⟫_ℝ)) := by
    fun_prop
  exact hcontinuous.exists_forall_le (tendsto_sum_exp_inner_atTop w a ha hzero)

/-- At a minimum of an exponential sum its weighted vector sum vanishes. -/
theorem sum_exp_inner_eq_zero_of_min (w : I → E) (a : I → ℝ) (t : E)
    (hmin : ∀ s : E, (∑ i, a i * Real.exp (2 * ⟪w i, t⟫_ℝ)) ≤
      ∑ i, a i * Real.exp (2 * ⟪w i, s⟫_ℝ)) :
    (∑ i, (a i * Real.exp (2 * ⟪w i, t⟫_ℝ)) • w i) = 0 := by
  let v : E := ∑ i, (a i * Real.exp (2 * ⟪w i, t⟫_ℝ)) • w i
  have hderiv : HasDerivAt
      (fun s : ℝ => ∑ i, a i * Real.exp (2 * ⟪w i, t + s • v⟫_ℝ))
      (∑ i, (a i * Real.exp (2 * ⟪w i, t⟫_ℝ)) * (2 * ⟪w i, v⟫_ℝ)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have hi := (((((hasDerivAt_id (0 : ℝ)).mul_const ⟪w i, v⟫_ℝ).const_add
      ⟪w i, t⟫_ℝ).const_mul 2).exp).const_mul (a i)
    simpa only [inner_add_right, inner_smul_right, one_mul, zero_mul, add_zero,
      mul_assoc, id_eq] using hi
  have hlocal : IsLocalMin
      (fun s : ℝ => ∑ i, a i * Real.exp (2 * ⟪w i, t + s • v⟫_ℝ)) 0 := by
    filter_upwards [] with s
    simpa only [zero_smul, add_zero] using hmin (t + s • v)
  have hzero := hlocal.hasDerivAt_eq_zero hderiv
  have hinner : (2 : ℝ) * ⟪v, v⟫_ℝ = 0 := by
    rw [show ⟪v, v⟫_ℝ = ∑ i, (a i * Real.exp (2 * ⟪w i, t⟫_ℝ)) *
        ⟪w i, v⟫_ℝ by simp only [v, sum_inner, real_inner_smul_left]]
    rw [Finset.mul_sum]
    convert hzero using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (by linarith)

/-- Positive exponential weights realize every point of the convex hull's intrinsic interior. -/
private theorem exists_centerMass_exp_inner [FiniteDimensional ℝ E]
    (w : I → E) (a : I → ℝ) (ha : ∀ i, 0 < a i) (q : E)
    (hq : q ∈ intrinsicInterior ℝ (convexHull ℝ (range w))) :
    ∃ t : E, Finset.univ.centerMass (fun i => a i * Real.exp (2 * ⟪w i, t⟫_ℝ)) w = q := by
  obtain ⟨qA, hqA, rfl⟩ := mem_intrinsicInterior.mp hq
  let : Nonempty (affineSpan ℝ (convexHull ℝ (range w))) := ⟨qA⟩
  let wA : I → affineSpan ℝ (convexHull ℝ (range w)) := fun i =>
    ⟨w i, subset_affineSpan ℝ _ (subset_convexHull ℝ _ (mem_range_self i))⟩
  have hzero := interior_convexHull_vsub _ wA qA hqA
  obtain ⟨t, ht⟩ := exists_min_sum_exp_inner (fun i => wA i -ᵥ qA) a ha hzero
  have hsum := sum_exp_inner_eq_zero_of_min (fun i => wA i -ᵥ qA) a t ht
  have hsumE : (∑ i, (a i * Real.exp (2 * ⟪w i - (qA : E), (t : E)⟫_ℝ)) •
      (w i - (qA : E))) = 0 := by
    have h := congrArg
      (fun x : (affineSpan ℝ (convexHull ℝ (range w))).direction => (x : E)) hsum
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
      Submodule.coe_inner, AffineSubspace.coe_vsub, vsub_eq_sub, wA] using h
  have hqmem := interior_subset hqA
  change (qA : E) ∈ convexHull ℝ (range w) at hqmem
  obtain ⟨_, ⟨i, _⟩⟩ := convexHull_nonempty_iff.mp ⟨(qA : E), hqmem⟩
  let : Nonempty I := ⟨i⟩
  have htotal : 0 < ∑ i, a i * Real.exp (2 * ⟪w i - (qA : E), (t : E)⟫_ℝ) :=
    Finset.sum_pos (fun i _ => mul_pos (ha i) (Real.exp_pos _)) Finset.univ_nonempty
  have hcenter : Finset.univ.centerMass
      (fun i => a i * Real.exp (2 * ⟪w i - (qA : E), (t : E)⟫_ℝ)) w = (qA : E) := by
    have hz : Finset.univ.centerMass
        (fun i => a i * Real.exp (2 * ⟪w i - (qA : E), (t : E)⟫_ℝ))
        (fun i => w i - (qA : E)) = 0 := by
      rw [Finset.centerMass, hsumE, smul_zero]
    rw [centerMass_sub _ _ _ htotal.ne'] at hz
    exact sub_eq_zero.mp hz
  refine ⟨(t : E), ?_⟩
  have hscale : Finset.univ.centerMass
      (fun i => a i * Real.exp (2 * ⟪w i - (qA : E), (t : E)⟫_ℝ)) w =
      Finset.univ.centerMass (fun i => a i * Real.exp (2 * ⟪w i, (t : E)⟫_ℝ)) w := by
    calc
      _ = Finset.univ.centerMass
          (Real.exp (-2 * ⟪(qA : E), (t : E)⟫_ℝ) •
            (fun i => a i * Real.exp (2 * ⟪w i, (t : E)⟫_ℝ))) w := by
        apply Finset.centerMass_congr_weights
        intro i _
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [show 2 * ⟪w i - (qA : E), (t : E)⟫_ℝ =
            -2 * ⟪(qA : E), (t : E)⟫_ℝ + 2 * ⟪w i, (t : E)⟫_ℝ by
          rw [inner_sub_left]; ring, Real.exp_add]
        ring
      _ = _ := Finset.centerMass_smul_left (t := Finset.univ)
        (w := fun i => a i * Real.exp (2 * ⟪w i, (t : E)⟫_ℝ)) (z := w)
        (Real.exp_ne_zero (-2 * ⟪(qA : E), (t : E)⟫_ℝ))
  exact hscale.symm.trans hcenter



end InnerProduct

section Normed
variable [NormedSpace ℝ E] [Fintype I]

/-- Linear functionals parameterize every intrinsic-interior exponential barycenter. -/
theorem exists_centerMass_exp_eq [FiniteDimensional ℝ E]
    (w : I → E) (a : I → ℝ) (ha : ∀ i, 0 < a i) (q : E)
    (hq : q ∈ intrinsicInterior ℝ (convexHull ℝ (range w))) :
    ∃ ℓ : E →L[ℝ] ℝ,
      Finset.univ.centerMass (fun i => a i * Real.exp (ℓ (w i))) w = q := by
  have htransport := (toEuclidean (E := E)).toContinuousAffineEquiv.intrinsicInterior_image
    (convexHull ℝ (range w))
  change intrinsicInterior ℝ ((toEuclidean (E := E)) '' convexHull ℝ (range w)) =
    (toEuclidean (E := E)) '' intrinsicInterior ℝ (convexHull ℝ (range w)) at htransport
  have hqE : toEuclidean q ∈ intrinsicInterior ℝ
      (convexHull ℝ (range (fun i => toEuclidean (w i)))) := by
    have hpoly := (toEuclidean (E := E)).toLinearMap.image_convexHull (range w)
    change (toEuclidean (E := E)) '' convexHull ℝ (range w) =
      convexHull ℝ ((toEuclidean (E := E)) '' range w) at hpoly
    rw [range_comp' (toEuclidean (E := E)) w, ← hpoly, htransport]
    exact mem_image_of_mem _ hq
  obtain ⟨t, ht⟩ := exists_centerMass_exp_inner
    (fun i => toEuclidean (w i)) a ha (toEuclidean q) hqE
  refine ⟨(2 : ℝ) • ((innerSL ℝ t).comp
    (toEuclidean (E := E)).toContinuousLinearMap), ?_⟩
  apply (toEuclidean (E := E)).injective
  simp only [Finset.centerMass, map_smul, map_sum]
  simpa only [Finset.centerMass, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    innerSL_apply_apply, real_inner_comm, smul_eq_mul] using ht


end Normed

end GroupActions
