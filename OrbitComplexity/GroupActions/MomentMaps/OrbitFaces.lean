import OrbitComplexity.GroupActions.MomentMaps.ClosureEquations
import OrbitComplexity.GroupActions.MomentMaps.CharacterExtension
import OrbitComplexity.GroupActions.MomentMaps.OrbitImage
import OrbitComplexity.GroupActions.MomentMaps.Degenerations
import Mathlib.Data.Setoid.Basic
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
import Batteries.Tactic.Lint

/-! # Orbits and faces of projective weight polytopes

Equal weight polytopes force equal coordinate supports inside a fixed projective
orbit closure. The homogeneous binomial equations give a character on that support;
extending it to the torus produces an orbit element. Its common scalar factor
preserves the projective point. The quotient of the closure points by the ambient
orbit relation is therefore equivalent to the nonempty exposed faces of the original
weight polytope, and the equivalence is computed by the weight polytope of each point.
Orbit moment images are relative interiors, orbit dimensions are affine dimensions,
and the moment image of the projective orbit closure is the original polytope.

## References

* E. Tsukerman and L. Williams, *Bruhat interval polytopes*, Adv. Math. 285 (2015), 766–810,
  Theorem 6.19.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Multiplicative TauCeti WithConv
open scoped Classical
noncomputable section
namespace GroupActions
universe u v w

private theorem dimension_of_finDim {n : ℕ} {d : WithBot ℕ∞} {a : WithBot ℕ}
    (hd : d = (n : WithBot ℕ∞)) (ha : a = (n : WithBot ℕ)) :
    d = WithBot.map (fun k : ℕ ↦ (k : ℕ∞)) a := by
  rw [hd, ha]
  rfl

/-- Two points in one diagonal projective orbit closure with equal weight polytopes
belong to the same torus orbit. -/
private theorem vector_orbit_of_polytope_eq {I J : Type} [Fintype I] [DecidableEq I] [Finite J]
    (χ : I → J →₀ ℤ) (v : I → ℂ) (hv : v ≠ 0)
    (x : I → ℂ) (hx : x ≠ 0) (y : I → ℂ) (hy : y ≠ 0) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i ↦ ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) I (I → ℂ)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    (projectiveVariety ℂ I).pointMap (projectiveVectorPoint x hx) ∈
      orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
        (projectiveVariety ℂ I) (projectiveVectorPoint v hv) →
      (projectiveVariety ℂ I).pointMap (projectiveVectorPoint y hy) ∈
        orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
          (projectiveVariety ℂ I) (projectiveVectorPoint v hv) →
      weightPolytope (fun i j ↦ (χ i j : ℝ)) (Projectivization.mk ℂ x hx) =
        weightPolytope (fun i j ↦ (χ i j : ℝ)) (Projectivization.mk ℂ y hy) →
      projectiveVectorPoint y hy ∈
        MulAction.orbit (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points
          (projectiveVectorPoint x hx) := by
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i ↦ ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) I (I → ℂ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  intro hcx hcy hpoly
  obtain ⟨_, _, hsx⟩ := projective_closure_face χ v hv x hx hcx
  obtain ⟨_, _, hsy⟩ := projective_closure_face χ v hv y hy hcy
  have hsupport (i : I) : x i ≠ 0 ↔ y i ≠ 0 := by rw [hsx i, hsy i, hpoly]
  obtain ⟨_, _, hbx⟩ := projective_closure_equations χ v hv x hx hcx
  obtain ⟨_, _, hby⟩ := projective_closure_equations χ v hv y hy hcy
  let f : Function.support x ↪ Function.support v :=
    ⟨fun i ↦ ⟨i.val, ((hsx i.val).mp i.property).1⟩,
      fun a b h ↦ Subtype.ext (congrArg (fun i : Function.support v ↦ i.val) h)⟩
  have hdx := binomial_relations_restrict
    (fun i : Function.support v ↦ ((1 : ℤ), χ i.val))
    (fun i : Function.support v ↦ x i.val / v i.val) hbx f
    (fun i : Function.support x ↦ ((1 : ℤ), χ i.val)) (fun _ ↦ rfl)
  have hdy := binomial_relations_restrict
    (fun i : Function.support v ↦ ((1 : ℤ), χ i.val))
    (fun i : Function.support v ↦ y i.val / v i.val) hby f
    (fun i : Function.support x ↦ ((1 : ℤ), χ i.val)) (fun _ ↦ rfl)
  have hdr := binomial_relations_div
    (fun i : Function.support x ↦ ((1 : ℤ), χ i.val))
    (fun i : Function.support x ↦ x (f i).val / v (f i).val)
    (fun i : Function.support x ↦ y (f i).val / v (f i).val) hdx hdy
  have hratio (i : Function.support x) :
      (y (f i).val / v (f i).val) / (x (f i).val / v (f i).val) = y i.val / x i.val :=
    div_div_div_cancel_right₀ (f i).property _ _
  let r : Function.support x → ℂˣ := fun i ↦
    Units.mk0 (y i.val / x i.val) (div_ne_zero ((hsupport i.val).mp i.property) i.property)
  have hr : ∀ d e : Function.support x → ℕ,
      weightMonoidHom (fun i : Function.support x ↦ ((1 : ℤ), χ i.val)) (ofAdd d) =
        weightMonoidHom (fun i : Function.support x ↦ ((1 : ℤ), χ i.val)) (ofAdd e) →
      ∏ i, r i ^ d i = ∏ i, r i ^ e i := by
    intro d e hde
    apply Units.ext
    have ht := hdr d e hde
    simp_rw [hratio] at ht
    simpa [r] using ht
  obtain ⟨s, τ, hτ⟩ := exists_homogeneous_character
    (fun i : Function.support x ↦ χ i.val) r hr
  let g := WithConv.toConv (DiagonalizableGroup.point (R := ℂ) τ)
  have hg (i : I) : g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1) =
      (τ (ofAdd (χ i)) : ℂ) := DiagonalizableGroup.point_single_one τ _
  have hscaled : (s : ℂ) •
      (fun i ↦ x i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1)) = y := by
    funext i
    change (s : ℂ) * (x i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1)) = y i
    by_cases hi : x i = 0
    · have hyi : y i = 0 := not_ne_iff.mp (fun hyi ↦ ((hsupport i).mpr hyi) hi)
      simp [hi, hyi]
    · have ht : y i / x i = (s : ℂ) * (τ (ofAdd (χ i)) : ℂ) := by
        simpa [r] using congrArg (fun u : ℂˣ ↦ (u : ℂ)) (hτ ⟨i, hi⟩)
      rw [hg]
      calc
        (s : ℂ) * (x i * (τ (ofAdd (χ i)) : ℂ)) =
            ((s : ℂ) * (τ (ofAdd (χ i)) : ℂ)) * x i := by ring
        _ = y i := by rw [← ht, div_mul_cancel₀ _ hi]
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨affineGroupPointsMulEquiv ℂ
    (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) g, ?_⟩
  rw [projective_weights_smul χ g x hx]
  have hw : (fun i ↦ x i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1)) ≠ 0 := by
    intro hzero
    apply hx
    funext i
    have ht := congrFun hzero i
    exact (mul_eq_zero.mp ht).resolve_right (by rw [hg]; exact Units.ne_zero _)
  have ht := (projectiveVectorPoint_scale _ hw s).symm
  simpa only [hscaled] using ht

/-- Equal weight polytopes identify the torus orbits of rational points in one
projective orbit closure. -/
theorem mem_orbit_of_weightPolytope_eq {I J : Type} [iFinite : Fintype I]
    [iDecidable : DecidableEq I] [jFinite : Finite J]
    (χ : I → J →₀ ℤ) (v : I → ℂ) (hv : v ≠ 0)
    (p q : (projectiveVariety ℂ I).points) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i ↦ ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) I (I → ℂ)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    (projectiveVariety ℂ I).pointMap p ∈
      orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
        (projectiveVariety ℂ I) (projectiveVectorPoint v hv) →
      (projectiveVariety ℂ I).pointMap q ∈
        orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
          (projectiveVariety ℂ I) (projectiveVectorPoint v hv) →
      weightPolytope (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm p) =
        weightPolytope (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm q) →
      q ∈ MulAction.orbit
        (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points p := by
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i ↦ ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) I (I → ℂ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  have hrep (z : I → ℂ) (hz : z ≠ 0) :
      projectivePointsEquiv.symm (projectiveVectorPoint z hz) = Projectivization.mk ℂ z hz := by
    simpa only [Equiv.symm_apply_apply] using
      (congrArg projectivePointsEquiv.symm (projectivePointsEquiv_mk z hz)).symm
  obtain ⟨px, rfl⟩ := projectivePointsEquiv.surjective p
  obtain ⟨py, rfl⟩ := projectivePointsEquiv.surjective q
  induction px using Projectivization.ind with
  | _ x hx =>
    induction py using Projectivization.ind with
    | _ y hy =>
      simpa only [projectivePointsEquiv_mk, hrep] using
        (@vector_orbit_of_polytope_eq I J iFinite iDecidable jFinite χ v hv x hx y hy)

/-- Nonempty exposed faces of the original weight polytope correspond bijectively to
ambient torus orbits represented in the projective orbit closure. -/
theorem exists_orbit_face_equiv {I J : Type} [iFintype : Fintype I]
    [iDecEq : DecidableEq I] [jFinite : Finite J]
    (χ : I → J →₀ ℤ) (v : I → ℂ) (hv : v ≠ 0) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i ↦ ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) I (I → ℂ)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    let C := {p : (projectiveVariety ℂ I).points // (projectiveVariety ℂ I).pointMap p ∈
      orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
        (projectiveVariety ℂ I) (projectiveVectorPoint v hv)}
    let r : Setoid C := Setoid.comap (fun p : C ↦ p.val)
      (MulAction.orbitRel
        (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points
        (projectiveVariety ℂ I).points)
    let Faces := {F : Set (J → ℝ) // F.Nonempty ∧ IsExposed ℝ
      (weightPolytope (fun i j ↦ (χ i j : ℝ)) (Projectivization.mk ℂ v hv)) F}
    ∃ e : Quotient r ≃ Faces, ∀ p : C, (e (Quotient.mk r p)).val =
      weightPolytope (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm p.val) := by
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i ↦ ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) I (I → ℂ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  let C := {p : (projectiveVariety ℂ I).points // (projectiveVariety ℂ I).pointMap p ∈
    orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
      (projectiveVariety ℂ I) (projectiveVectorPoint v hv)}
  let r : Setoid C := Setoid.comap (fun p : C ↦ p.val)
    (MulAction.orbitRel
      (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points
      (projectiveVariety ℂ I).points)
  let Faces := {F : Set (J → ℝ) // F.Nonempty ∧ IsExposed ℝ
    (weightPolytope (fun i j ↦ (χ i j : ℝ)) (Projectivization.mk ℂ v hv)) F}
  have hfaces (p : (projectiveVariety ℂ I).points)
      (hp : (projectiveVariety ℂ I).pointMap p ∈
        orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
          (projectiveVariety ℂ I) (projectiveVectorPoint v hv)) :
      (weightPolytope (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm p)).Nonempty ∧
        IsExposed ℝ
          (weightPolytope (fun i j ↦ (χ i j : ℝ)) (Projectivization.mk ℂ v hv))
          (weightPolytope (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm p)) := by
    obtain ⟨q, rfl⟩ := projectivePointsEquiv.surjective p
    induction q using Projectivization.ind with
    | _ y hy =>
      have ht := projective_closure_face χ v hv y hy hp
      simpa only [Equiv.symm_apply_apply] using And.intro ht.1 ht.2.1
  let f : C → Faces := fun p ↦
    ⟨weightPolytope (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm p.val),
      hfaces p.val p.property⟩
  have hker : ∀ a b : C, f a = f b ↔ r a b := by
    intro a b
    constructor
    · intro hab
      change a.val ∈ MulAction.orbit
        (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points b.val
      apply @mem_orbit_of_weightPolytope_eq I J iFintype iDecEq jFinite
        χ v hv b.val a.val b.property a.property
      exact (congrArg (fun F : Faces ↦ F.val) hab).symm
    · intro hab
      change a.val ∈ MulAction.orbit
        (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points b.val at hab
      obtain ⟨t, ht⟩ := MulAction.mem_orbit_iff.mp hab
      apply Subtype.ext
      change weightPolytope (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm a.val) =
        weightPolytope (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm b.val)
      rw [← ht]
      exact @projective_weightPolytope_smul I J iFintype iDecEq jFinite χ t b.val
  have hsurj : Function.Surjective f := by
    intro F
    have hF : IsExposed ℝ
        (convexHull ℝ ((fun i j ↦ (χ i j : ℝ)) '' Function.support v)) F.val := by
      simpa only [weightPolytope_mk] using F.property.2
    obtain ⟨hy, hmem, heq⟩ := exposed_face_point χ v hv hF F.property.1
    refine ⟨⟨projectiveVectorPoint _ hy, hmem⟩, Subtype.ext ?_⟩
    change weightPolytope (fun i j ↦ (χ i j : ℝ))
      (projectivePointsEquiv.symm (projectiveVectorPoint _ hy)) = F.val
    have hrep := congrArg projectivePointsEquiv.symm (projectivePointsEquiv_mk _ hy)
    simp only [Equiv.symm_apply_apply] at hrep
    rw [← hrep, weightPolytope_mk]
    exact heq
  obtain ⟨e, he⟩ := @exists_quotient_equiv C Faces r f hsurj hker
  exact ⟨e, fun p ↦ congrArg (fun F : Faces ↦ F.val) (he p)⟩

/-- Theorem 6.19 of Tsukerman–Williams: projective torus orbits correspond to nonempty exposed
faces, their moment images are relative interiors, their dimensions are affine dimensions, and
the closure image is the original weight polytope. -/
theorem projective_moment_faces {I J : Type} [iFintype : Fintype I]
    [iDecEq : DecidableEq I] [jFintype : Fintype J]
    (χ : I → J →₀ ℤ) (v : I → ℂ) (hv : v ≠ 0) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i ↦ ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) I (I → ℂ)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    let C := {p : (projectiveVariety ℂ I).points // (projectiveVariety ℂ I).pointMap p ∈
      orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
        (projectiveVariety ℂ I) (projectiveVectorPoint v hv)}
    let r : Setoid C := Setoid.comap (fun p : C ↦ p.val)
      (MulAction.orbitRel
        (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points
        (projectiveVariety ℂ I).points)
    let Faces := {F : Set (J → ℝ) // F.Nonempty ∧ IsExposed ℝ
      (weightPolytope (fun i j ↦ (χ i j : ℝ)) (Projectivization.mk ℂ v hv)) F}
    ∃ e : Quotient r ≃ Faces,
      (∀ p : C, (e (Quotient.mk r p)).val =
        weightPolytope (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm p.val)) ∧
      Set.range (fun p : {p : Projectivization ℂ (I → ℂ) //
          (projectiveVariety ℂ I).pointMap (projectivePointsEquiv p) ∈
            orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
              (projectiveVariety ℂ I) (projectiveVectorPoint v hv)} ↦
        momentMap (fun i j ↦ (χ i j : ℝ)) p.val) =
          weightPolytope (fun i j ↦ (χ i j : ℝ)) (Projectivization.mk ℂ v hv) ∧
      ∀ p : (projectiveVariety ℂ I).points,
        Set.range (fun t : (affineVariety ℂ
            (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points ↦
          momentMap (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm (t • p))) =
          intrinsicInterior ℝ
            (weightPolytope (fun i j ↦ (χ i j : ℝ)) (projectivePointsEquiv.symm p)) ∧
        orbitDim (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
            (projectiveVariety ℂ I) p =
          WithBot.map (fun n : ℕ ↦ (n : ℕ∞))
            (affineSpan ℝ (weightPolytope (fun i j ↦ (χ i j : ℝ))
              (projectivePointsEquiv.symm p))).finDim := by
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i ↦ ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) I (I → ℂ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  obtain ⟨e, he⟩ := @exists_orbit_face_equiv I J iFintype iDecEq inferInstance χ v hv
  refine ⟨e, he, ?_, ?_⟩
  · exact @projective_closure_moment_image I J iFintype iDecEq jFintype χ v hv
  · intro p
    obtain ⟨q, rfl⟩ := projectivePointsEquiv.surjective p
    induction q using Projectivization.ind with
    | _ x hx =>
      have hmoment := @projective_orbit_moment_image I J iFintype iDecEq jFintype χ x hx
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
      have hdim := @projective_orbit_polytope_dim I J iFintype iDecEq inferInstance
        χ x hx i₀ hi₀
      have hdim' := dimension_of_finDim hdim.1 hdim.2
      simp only [Equiv.symm_apply_apply]
      simpa only [projectivePointsEquiv_mk] using And.intro hmoment hdim'

/-- If singleton support polytopes satisfy a predicate, all support faces are realized,
and the supports of points satisfying the predicate lie in a convex set, then every
supported weight polytope lies in that convex set. -/
theorem weightPolytope_subset_of_fixed {I E X : Type*} [Fintype I]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    (weight : I → E) (f : X → Projectivization ℂ (I → ℂ))
    (fixed : X → Prop) (Q : Set E) (hQ : Convex ℝ Q)
    (hSingleton : ∀ x q, GroupActions.weightPolytope weight (f x) = {q} → fixed x)
    (hFixed : ∀ x, fixed x → GroupActions.weightPolytope weight (f x) ⊆ Q)
    (hFace : ∀ x F, F.Nonempty →
      IsExposed ℝ (GroupActions.weightPolytope weight (f x)) F →
        ∃ y, GroupActions.weightPolytope weight (f y) = F) :
    ∀ x, GroupActions.weightPolytope weight (f x) ⊆ Q := by
  classical
  intro x
  generalize hfx : f x = p
  induction p using Projectivization.ind with
  | _ v hv =>
    have hP : GroupActions.weightPolytope weight (f x) = convexHull ℝ
        (Set.range (fun i : {i : I // v i ≠ 0} => weight i.val)) := by
      rw [hfx, GroupActions.weightPolytope_mk]
      congr 1
      ext z
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.property, rfl⟩
    have hsubset : GroupActions.weightPolytope weight (f x) ⊆ Q := by
      rw [hP]
      apply GroupActions.finite_hull_subset_of_vertices
        (fun i : {i : I // v i ≠ 0} => weight i.val) hQ
      intro q hq
      have hq' : IsExposed ℝ (GroupActions.weightPolytope weight (f x)) {q} := by
        rw [hP]
        exact hq
      obtain ⟨y, hy⟩ := hFace x {q} (Set.singleton_nonempty q) hq'
      apply hFixed y (hSingleton y q hy)
      rw [hy]
      exact Set.mem_singleton q
    simpa only [hfx] using hsubset


end GroupActions
