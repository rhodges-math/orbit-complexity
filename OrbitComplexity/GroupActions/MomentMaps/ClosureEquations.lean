import OrbitComplexity.GroupActions.Tori.ProjectiveOrbitRank
import OrbitComplexity.GroupActions.MomentMaps.Faces
import Batteries.Tactic.Lint

/-! # Homogeneous equations on projective orbit closures

Homogeneous polynomial zero loci are Zariski closed in projective space. The lattice
binomials of a diagonal orbit therefore vanish on its scheme closure. Coordinates
outside the original support vanish, and division by its nonzero coordinates gives
a nonzero solution of the homogeneous binomials on that support. Its weight polytope
is an exposed face, with the support equal to the preimage of the face in the original support.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Multiplicative TauCeti WithConv
open MvPolynomial
open scoped Classical
noncomputable section
namespace GroupActions
universe u
variable {K I J : Type u} [Field K] [Fintype I] [DecidableEq I] [Finite J]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [DecidableEq I] in
private theorem eval_zero_on_closure
    (S : Set (projectiveVariety K I).points) (y : I → K) (hy : y ≠ 0)
    (hclosure : (projectiveVariety K I).pointMap (projectiveVectorPoint y hy) ∈
      (projectiveVariety K I).pointClosure S)
    (p : MvPolynomial I K) (n : ℕ) (hn : 0 < n) (hp : p.IsHomogeneous n)
    (hS : ∀ x ∈ S, p ∈ ((projectiveVariety K I).pointMap x).asHomogeneousIdeal) :
    eval y p = 0 := by
  apply (projectiveVectorPoint_mem y hy n hn p hp).mp
  have hc : (projectiveVariety K I).pointClosure S ⊆
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule I K) {p} := by
    apply closure_minimal
    · rintro _ ⟨x, hx, rfl⟩
      exact Set.singleton_subset_iff.mpr (hS x hx)
    · exact ProjectiveSpectrum.isClosed_zeroLocus _ _
  exact (hc hclosure) (Set.mem_singleton p)

omit [DecidableEq I] [Finite J] in
private theorem character_products_eq (χ : I → J →₀ ℤ)
    (g : MonoidAlgebra K (Multiplicative (J →₀ ℤ)) →ₐ[K] K)
    (d e : I → ℕ)
    (hde : weightMonoidHom (fun i ↦ ((1 : ℤ), χ i)) (ofAdd d) =
      weightMonoidHom (fun i ↦ ((1 : ℤ), χ i)) (ofAdd e)) :
    ∏ i, g (MonoidAlgebra.single (ofAdd (χ i)) 1) ^ d i =
      ∏ i, g (MonoidAlgebra.single (ofAdd (χ i)) 1) ^ e i := by
  classical
  let D : I →₀ ℕ := Finsupp.equivFunOnFinite.symm d
  let E : I →₀ ℕ := Finsupp.equivFunOnFinite.symm e
  let p : MvPolynomial I K := monomial D 1 - monomial E 1
  have hp : p ∈ RingHom.ker
      (weightPolynomialMap (K := K) (fun i ↦ ((1 : ℤ), χ i))).toRingHom := by
    rw [weightPolynomialMap_ker]
    exact Ideal.subset_span ⟨D, E, hde, rfl⟩
  let a : MonoidAlgebra K (Multiplicative (ℤ × (J →₀ ℤ))) →ₐ[K] K :=
    g.comp (MonoidAlgebra.mapDomainAlgHom K K
      (AddMonoidHom.snd ℤ (J →₀ ℤ)).toMultiplicative)
  have hfactor : a.comp (weightPolynomialMap (K := K) (fun i ↦ ((1 : ℤ), χ i))) =
      MvPolynomial.aeval (fun i ↦ g (MonoidAlgebra.single (ofAdd (χ i)) 1)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, weightPolynomialMap_X, MvPolynomial.aeval_X]
    change g (MonoidAlgebra.mapDomain _ (MonoidAlgebra.single _ 1)) = _
    rw [MonoidAlgebra.mapDomain_single]
    rfl
  have hz := congrArg a
    (show weightPolynomialMap (K := K) (fun i ↦ ((1 : ℤ), χ i)) p = 0 from hp)
  change (a.comp (weightPolynomialMap (K := K) (fun i ↦ ((1 : ℤ), χ i)))) p = a 0 at hz
  rw [hfactor, map_zero] at hz
  apply sub_eq_zero.mp
  simpa [p, D, E, MvPolynomial.aeval_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype] using hz

omit [DecidableEq I] [Finite J] in
private theorem normalized_monomial_eval (d : I → ℕ) (a b : I → K) :
    eval b (monomial (Finsupp.equivFunOnFinite.symm d) ((∏ i, a i ^ d i)⁻¹)) =
      ∏ i, (b i / a i) ^ d i := by
  classical
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib]
  simp [eval_monomial, Finsupp.prod_fintype, div_eq_mul_inv, mul_comm]

omit [DecidableEq I] [Finite J] in
private theorem equal_weight_degree (χ : I → J →₀ ℤ) (d e : I → ℕ)
    (hde : weightMonoidHom (fun i ↦ ((1 : ℤ), χ i)) (ofAdd d) =
      weightMonoidHom (fun i ↦ ((1 : ℤ), χ i)) (ofAdd e)) :
    ∑ i, d i = ∑ i, e i := by
  have ht := congrArg (fun x : Multiplicative (ℤ × (J →₀ ℤ)) ↦ (toAdd x).1) hde
  change (Fintype.linearCombination ℕ (fun i ↦ ((1 : ℤ), χ i)) d).1 =
    (Fintype.linearCombination ℕ (fun i ↦ ((1 : ℤ), χ i)) e).1 at ht
  simp only [Fintype.linearCombination_apply, Prod.fst_sum, Prod.smul_fst,
    nsmul_eq_mul, mul_one] at ht
  exact_mod_cast ht

omit [Fintype I] [DecidableEq I] [Finite J] in
private theorem image_ratio_support {E : Type*} (w : I → E) (v y : I → K)
    (hzero : ∀ i, v i = 0 → y i = 0) :
    (fun i : Function.support v ↦ w i.val) ''
        Function.support (fun i : Function.support v ↦ y i.val / v i.val) =
      w '' Function.support y := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, (div_ne_zero_iff.mp hi).1, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hvi : v i ≠ 0 := fun h ↦ hi (hzero i h)
    exact ⟨⟨i, hvi⟩, div_ne_zero hi hvi, rfl⟩

variable [IsAlgClosed K]

private theorem orbit_eval_zero (χ : I → J →₀ ℤ) (v : I → K) (hv : v ≠ 0)
    (y : I → K) (hy : y ≠ 0) (p : MvPolynomial I K) (n : ℕ) (hn : 0 < n)
    (hp : p.IsHomogeneous n)
    (hvanish : ∀ g : WithConv (MonoidAlgebra K (Multiplicative (J →₀ ℤ)) →ₐ[K] K),
      eval (fun i ↦ v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1)) p = 0) :
    letI : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
      Comodule.ofWeights (Pi.basisFun K I) (fun i ↦ ofAdd (χ i))
    letI := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun K I)
    (projectiveVariety K I).pointMap (projectiveVectorPoint y hy) ∈
      orbitClosure (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))))
        (projectiveVariety K I) (projectiveVectorPoint v hv) → eval y p = 0 := by
  let : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
    Comodule.ofWeights (Pi.basisFun K I) (fun i ↦ ofAdd (χ i))
  let := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun K I)
  intro hclosure
  apply eval_zero_on_closure _ y hy hclosure p n hn hp
  intro x hx
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  obtain ⟨g, rfl⟩ := (affineGroupPointsMulEquiv K
    (MonoidAlgebra K (Multiplicative (J →₀ ℤ)))).surjective g
  rw [projective_weights_smul χ g v hv]
  exact (projectiveVectorPoint_mem _ _ n hn p hp).mpr (hvanish g)

/-- A point of a diagonal projective orbit closure vanishes outside the original support;
on that support its coordinate ratios satisfy all homogeneous lattice binomials. -/
theorem projective_closure_equations (χ : I → J →₀ ℤ) (v : I → K) (hv : v ≠ 0)
    (y : I → K) (hy : y ≠ 0) :
    letI : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
      Comodule.ofWeights (Pi.basisFun K I) (fun i ↦ ofAdd (χ i))
    letI := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun K I)
    (projectiveVariety K I).pointMap (projectiveVectorPoint y hy) ∈
      orbitClosure (affineVariety K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))))
        (projectiveVariety K I) (projectiveVectorPoint v hv) →
      (∀ i, v i = 0 → y i = 0) ∧
        (fun i : Function.support v ↦ y i.val / v i.val) ≠ 0 ∧
        ∀ d e : Function.support v → ℕ,
          weightMonoidHom (fun i : Function.support v ↦ ((1 : ℤ), χ i.val)) (ofAdd d) =
            weightMonoidHom (fun i : Function.support v ↦ ((1 : ℤ), χ i.val)) (ofAdd e) →
          ∏ i : Function.support v, (y i.val / v i.val) ^ d i =
            ∏ i : Function.support v, (y i.val / v i.val) ^ e i := by
  let : Comodule K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) (I → K) :=
    Comodule.ofWeights (Pi.basisFun K I) (fun i ↦ ofAdd (χ i))
  let := @comoduleProjectiveAction K (MonoidAlgebra K (Multiplicative (J →₀ ℤ))) I (I → K)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun K I)
  intro hclosure
  have hzero (i : I) (hi : v i = 0) : y i = 0 := by
    have ht := orbit_eval_zero χ v hv y hy (X i) 1 Nat.zero_lt_one
      (isHomogeneous_X K i) (fun g ↦ by simp [hi]) hclosure
    simpa only [eval_X] using ht
  refine ⟨hzero, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have hvi : v i ≠ 0 := fun h ↦ hi (hzero i h)
    intro h
    exact (div_ne_zero hi hvi) (congrFun h ⟨i, hvi⟩)
  · intro d e hde
    have hdeg := equal_weight_degree (fun i : Function.support v ↦ χ i.val) d e hde
    by_cases hn : ∑ i, d i = 0
    · have hd0 : d = 0 := funext fun i ↦
        (Finset.sum_eq_zero_iff.mp hn) i (Finset.mem_univ i)
      have he0 : e = 0 := funext fun i ↦ (Finset.sum_eq_zero_iff.mp (hdeg.symm.trans hn)) i
        (Finset.mem_univ i)
      simp only [hd0, he0, Pi.zero_apply, pow_zero, Finset.prod_const_one]
    · have hnpos : 0 < ∑ i, d i := Nat.pos_of_ne_zero hn
      let p : MvPolynomial I K := rename Subtype.val
        (monomial (Finsupp.equivFunOnFinite.symm d) ((∏ i, v i.val ^ d i)⁻¹) -
          monomial (Finsupp.equivFunOnFinite.symm e) ((∏ i, v i.val ^ e i)⁻¹))
      have hp : p.IsHomogeneous (∑ i, d i) := by
        apply IsHomogeneous.rename_isHomogeneous
        apply IsHomogeneous.sub
        · exact isHomogeneous_monomial _ (by simp [Finsupp.degree_eq_sum])
        · exact isHomogeneous_monomial _
            (by simpa [Finsupp.degree_eq_sum] using hdeg.symm)
      have hpeval (b : I → K) : eval b p =
          (∏ i : Function.support v, (b i.val / v i.val) ^ d i) -
            (∏ i : Function.support v, (b i.val / v i.val) ^ e i) := by
        dsimp only [p]
        rw [eval_rename, map_sub, normalized_monomial_eval, normalized_monomial_eval]
        rfl
      have hvanish (g : WithConv (MonoidAlgebra K (Multiplicative (J →₀ ℤ)) →ₐ[K] K)) :
          eval (fun i ↦ v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1)) p = 0 := by
        rw [hpeval]
        have hratio (i : Function.support v) :
            (v i.val * g.ofConv (MonoidAlgebra.single (ofAdd (χ i.val)) 1)) / v i.val =
              g.ofConv (MonoidAlgebra.single (ofAdd (χ i.val)) 1) :=
          mul_div_cancel_left₀ _ i.property
        simp_rw [hratio]
        exact sub_eq_zero.mpr
          (character_products_eq (fun i : Function.support v ↦ χ i.val) g.ofConv d e hde)
      have heval := orbit_eval_zero χ v hv y hy p (∑ i, d i) hnpos hp hvanish hclosure
      rw [hpeval] at heval
      exact sub_eq_zero.mp heval

/-- The weight polytope of a projective orbit-closure point is a nonempty exposed face;
its coordinate support is exactly the preimage of that face in the original support. -/
theorem projective_closure_face {I J : Type} [Fintype I] [DecidableEq I] [Finite J]
    (χ : I → J →₀ ℤ) (v : I → ℂ) (hv : v ≠ 0)
    (y : I → ℂ) (hy : y ≠ 0) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i ↦ ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) I (I → ℂ)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    (projectiveVariety ℂ I).pointMap (projectiveVectorPoint y hy) ∈
      orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
        (projectiveVariety ℂ I) (projectiveVectorPoint v hv) →
      (weightPolytope (fun i j ↦ (χ i j : ℝ)) (Projectivization.mk ℂ y hy)).Nonempty ∧
        IsExposed ℝ
          (weightPolytope (fun i j ↦ (χ i j : ℝ)) (Projectivization.mk ℂ v hv))
          (weightPolytope (fun i j ↦ (χ i j : ℝ)) (Projectivization.mk ℂ y hy)) ∧
        ∀ i, y i ≠ 0 ↔ v i ≠ 0 ∧ (fun j ↦ (χ i j : ℝ)) ∈
          weightPolytope (fun k j ↦ (χ k j : ℝ)) (Projectivization.mk ℂ y hy) := by
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i ↦ ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) I (I → ℂ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  intro hclosure
  obtain ⟨hzero, hz, hbin⟩ := projective_closure_equations χ v hv y hy hclosure
  let _ : Fintype J := Fintype.ofFinite J
  obtain ⟨hne, hface, hsupport⟩ := binomial_support_face
    (fun i : Function.support v ↦ χ i.val)
    (fun i : Function.support v ↦ y i.val / v i.val) hz hbin
  have hrange : Set.range (fun (i : Function.support v) j ↦ (χ i.val j : ℝ)) =
      (fun i j ↦ (χ i j : ℝ)) '' Function.support v :=
    (Set.image_eq_range (fun i j ↦ (χ i j : ℝ)) (Function.support v)).symm
  have himage := image_ratio_support (fun i j ↦ (χ i j : ℝ)) v y hzero
  rw [hrange, himage] at hface
  rw [himage] at hne hsupport
  simp only [weightPolytope_mk]
  refine ⟨hne, hface, ?_⟩
  intro i
  constructor
  · intro hi
    have hvi : v i ≠ 0 := fun h ↦ hi (hzero i h)
    exact ⟨hvi, (hsupport ⟨i, hvi⟩).mpr (div_ne_zero hi hvi)⟩
  · rintro ⟨hvi, hi⟩
    exact (div_ne_zero_iff.mp ((hsupport ⟨i, hvi⟩).mp hi)).1

end GroupActions
