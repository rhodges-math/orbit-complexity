import OrbitComplexity.GroupActions.Tori.ProjectiveOrbitRank
import OrbitComplexity.GroupActions.MomentMaps.FaceInteriors
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
import Mathlib.Algebra.Polynomial.Laurent
import OrbitComplexity.GroupActions.MomentMaps.RationalSeparation
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Jensen
import Mathlib.LinearAlgebra.StdBasis
import Batteries.Tactic.Lint

/-! # Integral cocharacters and projective degenerations

A real exposing functional on a finite integral weight hull can be replaced by
an integral functional with the same maximizing weights. The corresponding
one-parameter curve specializes to the coordinates on that face. Its value at
zero belongs to the scheme orbit closure by density of the Laurent parameter.

## Main results

* GroupActions.exists_integer_exposing: an integral exposing form and a maximizing weight.
* GroupActions.cocharacter_face_point: specialization along a cocharacter.
* GroupActions.exposed_face_point: face coordinates belong to the projective orbit closure.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Multiplicative TauCeti WithConv
open Set Matrix
noncomputable section
namespace GroupActions
universe u v
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

private theorem form_coordinates (ℓ : StrongDual ℝ (J → ℝ)) (a : J → ℝ) :
    ∑ j, a j * ℓ ((Pi.basisFun ℝ J) j) = ℓ a := by
  have h := congrArg ℓ ((Pi.basisFun ℝ J).sum_repr a)
  simpa only [map_sum, map_smul, Pi.basisFun_repr, smul_eq_mul] using h

private theorem integral_coefficients (q : J → ℚ) :
    ∃ h : (J →₀ ℤ) →+ ℤ, ∃ c : ℤ, 0 < c ∧
      ∀ a, (h a : ℚ) = (c : ℚ) * ∑ j, (a j : ℚ) * q j := by
  obtain ⟨c, hc, n, hn⟩ := exists_pos_integer_multiple q
  let h : (J →₀ ℤ) →+ ℤ :=
    { toFun := fun a => ∑ j, a j * n j
      map_zero' := by simp
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib] }
  refine ⟨h, c, hc, ?_⟩
  intro a
  change ((∑ j, a j * n j : ℤ) : ℚ) = _
  push_cast
  simp_rw [hn]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A nonempty exposed face of a finite integral weight hull has an integral exposing form. -/
theorem exists_integer_exposing (χ : I → J →₀ ℤ) {F : Set (J → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range (fun i j => (χ i j : ℝ)))) F)
    (hne : F.Nonempty) :
    ∃ h : (J →₀ ℤ) →+ ℤ, ∃ m : ℤ, ∃ i₀ : I,
      (fun j => (χ i₀ j : ℝ)) ∈ F ∧ (∀ i, h (χ i) ≤ m) ∧
        ∀ i, (fun j => (χ i j : ℝ)) ∈ F ↔ h (χ i) = m := by
  classical
  obtain ⟨ℓ, i₀, _hface, hi₀, hle, heq⟩ :=
    @exists_exposing_vertex I (J → ℝ) inferInstance inferInstance inferInstance
      (fun i j => (χ i j : ℝ)) F hF hne
  let x : J → ℝ := fun j => ℓ ((Pi.basisFun ℝ J) j)
  let A : Matrix {i : I // (fun j => (χ i j : ℝ)) ∈ F} J ℚ :=
    fun i j => ((χ i.val j - χ i₀ j : ℤ) : ℚ)
  have hdot (i : I) :
      (∑ j, ((χ i j - χ i₀ j : ℤ) : ℝ) * x j) =
        ℓ (fun j => (χ i j : ℝ)) - ℓ (fun j => (χ i₀ j : ℝ)) := by
    rw [← map_sub]
    simpa only [Pi.sub_apply, Int.cast_sub, x] using
      form_coordinates ℓ ((fun j => (χ i j : ℝ)) - (fun j => (χ i₀ j : ℝ)))
  have hx : A.map (algebraMap ℚ ℝ) *ᵥ x = 0 := by
    ext i
    change (∑ j, (((χ i.val j - χ i₀ j : ℤ) : ℚ) : ℝ) * x j) = 0
    simp only [Rat.cast_intCast]
    rw [hdot]
    exact sub_eq_zero.mpr ((heq i.val).mp i.property)
  let U : Set (J → ℝ) :=
    ⋂ i ∈ Finset.univ.filter (fun i => (fun j => (χ i j : ℝ)) ∉ F),
      {y | ∑ j, ((χ i j - χ i₀ j : ℤ) : ℝ) * y j < 0}
  have hU : IsOpen U := by
    apply isOpen_biInter_finset
    intro i _
    exact isOpen_lt (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_apply j)) continuous_const
  have hxU : x ∈ U := by
    refine Set.mem_iInter₂.mpr ?_
    intro i hi
    change (∑ j, ((χ i j - χ i₀ j : ℤ) : ℝ) * x j) < 0
    rw [hdot, sub_neg]
    exact lt_of_le_of_ne (hle i)
      (fun h => (Finset.mem_filter.mp hi).2 ((heq i).mpr h))
  obtain ⟨q, hq, hqU⟩ := exists_rat_kernel_open A x hx U hU hxU
  obtain ⟨h, c, hc, hcoeff⟩ := integral_coefficients q
  have hscale (i : I) :
      ((h (χ i) - h (χ i₀) : ℤ) : ℚ) =
        (c : ℚ) * ∑ j, ((χ i j - χ i₀ j : ℤ) : ℚ) * q j := by
    rw [Int.cast_sub, hcoeff, hcoeff, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have hzero (i : I) (hi : (fun j => (χ i j : ℝ)) ∈ F) :
      h (χ i) = h (χ i₀) := by
    have ht := congrFun hq ⟨i, hi⟩
    change (∑ j, ((χ i j - χ i₀ j : ℤ) : ℚ) * q j) = 0 at ht
    have hz : ((h (χ i) - h (χ i₀) : ℤ) : ℚ) = 0 := by
      rw [hscale, ht, mul_zero]
    exact sub_eq_zero.mp (by exact_mod_cast hz)
  have hstrict (i : I) (hi : (fun j => (χ i j : ℝ)) ∉ F) :
      h (χ i) < h (χ i₀) := by
    have ht : ∑ j, ((χ i j - χ i₀ j : ℤ) : ℝ) * (q j : ℝ) < 0 :=
      (Set.mem_iInter₂.mp hqU) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    have htQ : ∑ j, ((χ i j - χ i₀ j : ℤ) : ℚ) * q j < 0 := by exact_mod_cast ht
    have hcQ : (0 : ℚ) < c := by exact_mod_cast hc
    have hz : ((h (χ i) - h (χ i₀) : ℤ) : ℚ) < 0 := by
      rw [hscale]
      exact mul_neg_of_pos_of_neg hcQ htQ
    have hzZ : h (χ i) - h (χ i₀) < 0 := by exact_mod_cast hz
    exact sub_neg.mp hzZ
  refine ⟨h, h (χ i₀), i₀, hi₀, ?_, ?_⟩
  · intro i
    by_cases hi : (fun j => (χ i j : ℝ)) ∈ F
    · exact (hzero i hi).le
    · exact (hstrict i hi).le
  · intro i
    constructor
    · exact hzero i
    · intro hi
      by_contra hn
      exact (hstrict i hn).ne hi


variable {K : Type u} [Field K] [IsAlgClosed K]

private instance laurentFiniteType : Algebra.FiniteType K (LaurentPolynomial K) :=
  AddMonoidAlgebra.finiteType_iff_group_fg.mpr
    (Module.Finite.iff_addGroup_fg.mp inferInstance)

private theorem dense_curve_mem {X Y Z : Variety K}
    (a : Z.toOver ⟶ X.toOver) (b : X.toOver ⟶ Y.toOver)
    (ha : DenseRange (a.left : Z.scheme → X.scheme))
    (S : Set Y.points) (hS : ∀ z, Variety.mapPoints (a ≫ b) z ∈ S) (x : X.points) :
    Y.pointMap (Variety.mapPoints b x) ∈ Y.pointClosure S := by
  have hr : Set.range (Variety.mapPoints (a ≫ b)) ⊆ S := by
    rintro _ ⟨z, rfl⟩
    exact hS z
  have himg : b.left (X.pointMap x) ∈ b.left '' closure
      (Set.range (a.left : Z.scheme → X.scheme)) := ⟨_, ha _, rfl⟩
  have hm := image_closure_subset_closure_image b.left.continuous himg
  rw [← Set.range_comp] at hm
  change b.left (X.pointMap x) ∈ closure (Set.range
    ((a ≫ b).left : Z.scheme → Y.scheme)) at hm
  rw [← Variety.pointClosure_range] at hm
  exact closure_mono (Set.image_mono hr) hm

omit [IsAlgClosed K] in
private theorem laurent_dense :
    DenseRange ((affineMorphism (Polynomial.toLaurentAlg (R := K))).left :
      (affineVariety K (LaurentPolynomial K)).scheme →
        (affineVariety K (Polynomial K)).scheme) := by
  change DenseRange (PrimeSpectrum.comap
    (Polynomial.toLaurentAlg (R := K)).toRingHom)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  have hi : Function.Injective (Polynomial.toLaurentAlg (R := K)).toRingHom :=
    Polynomial.toLaurent_injective
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hi]
  exact bot_le

omit [IsAlgClosed K] in
private theorem laurent_parameter_ne_zero (g : LaurentPolynomial K →ₐ[K] K) :
    g (LaurentPolynomial.T 1) ≠ 0 := by
  exact ((LaurentPolynomial.isUnit_T (1 : ℤ)).map g).ne_zero

variable {I J : Type u} [Fintype I] [DecidableEq I] [Finite J]

/-- A cocharacter maximum is reached by an algebraic one-parameter degeneration. -/
theorem cocharacter_face_point (χ : I → J →₀ ℤ) (v : I → K) (hv : v ≠ 0)
    (h : (J →₀ ℤ) →+ ℤ) (m : ℤ) (i₀ : I) (hi₀ : v i₀ ≠ 0)
    (hbase : h (χ i₀) = m) (hbound : ∀ i, v i ≠ 0 → h (χ i) ≤ m) :
    letI : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
      Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))
      I (I → K) inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun K I)
    let y := fun i => if h (χ i) = m then v i else 0
    ∃ hy : y ≠ 0, (projectiveVariety K I).pointMap (projectiveVectorPoint y hy) ∈
      orbitClosure (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))))
        (projectiveVariety K I) (projectiveVectorPoint v hv) := by
  classical
  let : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
    Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))
    I (I → K) inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun K I)
  let y := fun i => if h (χ i) = m then v i else 0
  have hy₀ : y i₀ ≠ 0 := by simpa only [y, hbase, ite_true] using hi₀
  have hy : y ≠ 0 := fun hz => hy₀ (congrFun hz i₀)
  refine ⟨hy, ?_⟩
  let P : MvPolynomial {i : I // i ≠ i₀} K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval (fun i => Polynomial.C (v i.val / v i₀) *
      Polynomial.X ^ (m - h (χ i.val)).toNat)
  have hP (i : {i : I // i ≠ i₀}) : P (MvPolynomial.X i) =
      Polynomial.C (v i.val / v i₀) * Polynomial.X ^ (m - h (χ i.val)).toNat :=
    MvPolynomial.aeval_X _ i
  let curve := affineMorphism P ≫ projectiveChartMorphism K I i₀
  let zeroPoint := (affineVarietyPointsEquiv K (Polynomial K)).symm (Polynomial.aeval (0 : K))
  have hzero : Variety.mapPoints curve zeroPoint = projectiveVectorPoint y hy := by
    rw [@projectiveVectorPoint_chart K I inferInstance inferInstance y hy i₀ hy₀]
    rw [Variety.mapPoints_comp]
    apply congrArg (Variety.mapPoints (projectiveChartMorphism K I i₀))
    apply (affineSpaceVarietyPointsEquiv K {i : I // i ≠ i₀}).injective
    funext i
    rw [Equiv.apply_symm_apply]
    have hc := @affineMorphism_coordinate K (Polynomial K) {i : I // i ≠ i₀}
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      P zeroPoint i
    refine hc.trans ?_
    rw [Equiv.apply_symm_apply, hP]
    change (Polynomial.aeval (0 : K))
      (Polynomial.C (v i.val / v i₀) * Polynomial.X ^ (m - h (χ i.val)).toNat) = _
    by_cases hi : v i.val = 0
    · simp [hi, y, hbase]
    · by_cases heq : h (χ i.val) = m
      · simp [y, heq, hbase]
      · have hpos : 0 < m - h (χ i.val) :=
          sub_pos.mpr (lt_of_le_of_ne (hbound i.val hi) heq)
        have hn : (m - h (χ i.val)).toNat ≠ 0 := by omega
        simp [y, heq, hbase, zero_pow hn]
  have hunit (z : (affineVariety K (LaurentPolynomial K)).points) :
      Variety.mapPoints (affineMorphism (Polynomial.toLaurentAlg (R := K)) ≫ curve) z ∈
        MulAction.orbit
          (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))).points
          (projectiveVectorPoint v hv) := by
    obtain ⟨g, rfl⟩ := (affineVarietyPointsEquiv K (LaurentPolynomial K)).symm.surjective z
    let t : K := g (LaurentPolynomial.T 1)
    have ht : t ≠ 0 := laurent_parameter_ne_zero g
    let tu : Kˣ := Units.mk0 t ht
    let character : Multiplicative (J →₀ ℤ) →* Kˣ :=
      (zpowersHom Kˣ tu).comp (AddMonoidHom.toMultiplicative (-h))
    let gH := WithConv.toConv (DiagonalizableGroup.point (R := K) character)
    have hchar (i : I) :
        gH.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1) = t ^ (-h (χ i)) := by
      change DiagonalizableGroup.point (R := K) character
        (MonoidAlgebra.single (ofAdd (χ i)) 1) = _
      rw [DiagonalizableGroup.point_single_one]
      exact Units.val_zpow_eq_zpow_val tu (-h (χ i))
    have hact₀ : v i₀ * t ^ (-h (χ i₀)) ≠ 0 :=
      mul_ne_zero hi₀ (zpow_ne_zero _ ht)
    have hact : (fun i => v i * t ^ (-h (χ i))) ≠ 0 := fun hz => hact₀ (congrFun hz i₀)
    have hsmul : affineGroupPointsMulEquiv K
        (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) gH • projectiveVectorPoint v hv =
        projectiveVectorPoint (fun i => v i * t ^ (-h (χ i))) hact := by
      simpa only [hchar] using
        (@projective_weights_smul K I J inferInstance inferInstance inferInstance
          inferInstance inferInstance χ gH v hv)
    rw [@projectiveVectorPoint_chart K I inferInstance inferInstance
      (fun i => v i * t ^ (-h (χ i))) hact i₀ hact₀] at hsmul
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨affineGroupPointsMulEquiv K
      (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) gH, ?_⟩
    rw [hsmul, Variety.mapPoints_comp, Variety.mapPoints_comp, affineMorphism_points]
    apply congrArg (Variety.mapPoints (projectiveChartMorphism K I i₀))
    apply (affineSpaceVarietyPointsEquiv K {i : I // i ≠ i₀}).injective
    funext i
    rw [Equiv.apply_symm_apply]
    have hc := @affineMorphism_coordinate K (Polynomial K) {i : I // i ≠ i₀}
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance P
      ((affineVarietyPointsEquiv K (Polynomial K)).symm
        (g.comp (Polynomial.toLaurentAlg (R := K)))) i
    refine Eq.trans ?_ hc.symm
    rw [Equiv.apply_symm_apply, hP]
    change (v i.val * t ^ (-h (χ i.val))) / (v i₀ * t ^ (-h (χ i₀))) =
      (g.comp (Polynomial.toLaurentAlg (R := K)))
        (Polynomial.C (v i.val / v i₀) * Polynomial.X ^ (m - h (χ i.val)).toNat)
    simp only [AlgHom.comp_apply, map_mul, map_pow,
      Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
    rw [LaurentPolynomial.C_eq_algebraMap, AlgHom.commutes, Algebra.algebraMap_self]
    change (v i.val * t ^ (-h (χ i.val))) / (v i₀ * t ^ (-h (χ i₀))) =
      (v i.val / v i₀) * t ^ (m - h (χ i.val)).toNat
    by_cases hi : v i.val = 0
    · simp [hi]
    · rw [mul_div_mul_comm, ← zpow_sub₀ ht]
      congr 1
      rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr (hbound i.val hi))]
      rw [hbase]
      congr 1
      omega
  have hm := dense_curve_mem (affineMorphism (Polynomial.toLaurentAlg (R := K))) curve
    laurent_dense (MulAction.orbit
      (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))).points
      (projectiveVectorPoint v hv)) hunit zeroPoint
  rw [hzero] at hm
  exact hm


/-- Truncation to an exposed face retains its hull and lies in the projective orbit closure. -/
theorem exposed_face_point (χ : I → J →₀ ℤ) (v : I → K) (hv : v ≠ 0)
    {F : Set (J → ℝ)}
    (hF : IsExposed ℝ
      (convexHull ℝ ((fun i j => (χ i j : ℝ)) '' Function.support v)) F)
    (hne : F.Nonempty) :
    letI : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
      Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))
      I (I → K) inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun K I)
    let y := fun i => @ite K ((fun j => (χ i j : ℝ)) ∈ F)
      (Classical.propDecidable _) (v i) 0
    ∃ hy : y ≠ 0, (projectiveVariety K I).pointMap (projectiveVectorPoint y hy) ∈
      orbitClosure (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))))
        (projectiveVariety K I) (projectiveVectorPoint v hv) ∧
      convexHull ℝ ((fun i j => (χ i j : ℝ)) '' Function.support y) = F := by
  classical
  let : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
    Comodule.ofWeights (Pi.basisFun K I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))
    I (I → K) inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun K I)
  have hset : (fun i j => (χ i j : ℝ)) '' Function.support v =
      Set.range (fun (i : {i : I // v i ≠ 0}) j => (χ i.val j : ℝ)) := by
    ext z
    simp
  have hF' : IsExposed ℝ
      (convexHull ℝ (Set.range (fun (i : {i : I // v i ≠ 0}) j => (χ i.val j : ℝ)))) F := by
    rwa [← hset]
  obtain ⟨h, m, i₀, hi₀, hbound, heq⟩ :=
    @exists_integer_exposing {i : I // v i ≠ 0} J inferInstance (Fintype.ofFinite J)
      (fun i => χ i.val) F hF' hne
  have hco := @cocharacter_face_point K inferInstance inferInstance I J
    inferInstance inferInstance inferInstance χ v hv h m i₀.val i₀.property
      ((heq i₀).mp hi₀) (fun i hi => hbound ⟨i, hi⟩)
  have hvector : (fun i => if h (χ i) = m then v i else 0) =
      (fun i => if (fun j => (χ i j : ℝ)) ∈ F then v i else 0) := by
    funext i
    by_cases hi : v i = 0
    · simp [hi]
    · simp only [← heq ⟨i, hi⟩]
  simp only [hvector] at hco
  obtain ⟨hy, hclose⟩ := hco
  refine ⟨hy, hclose, ?_⟩
  have hysupport :
      (fun i j => (χ i j : ℝ)) ''
        Function.support (fun i => if (fun j => (χ i j : ℝ)) ∈ F then v i else 0) =
      (fun (i : {i : I // v i ≠ 0}) j => (χ i.val j : ℝ)) ''
        {i | (fun j => (χ i.val j : ℝ)) ∈ F} := by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      change (if (fun j => (χ i j : ℝ)) ∈ F then v i else 0) ≠ 0 at hi
      have hfi : (fun j => (χ i j : ℝ)) ∈ F := by
        by_contra hn
        exact hi (by simp [hn])
      have hvi : v i ≠ 0 := by simpa only [ite_eq_left hfi] using hi
      exact ⟨⟨i, hvi⟩, hfi, rfl⟩
    · rintro ⟨⟨i, hi⟩, hfi, rfl⟩
      change (fun j => (χ i j : ℝ)) ∈ F at hfi
      refine ⟨i, ?_, rfl⟩
      change (if (fun j => (χ i j : ℝ)) ∈ F then v i else 0) ≠ 0
      simpa only [ite_eq_left hfi] using hi
  rw [hysupport]
  exact @exposed_hull_eq {i : I // v i ≠ 0} (J → ℝ)
    inferInstance inferInstance inferInstance inferInstance
    (fun i j => (χ i.val j : ℝ)) F hF' hne

end GroupActions
