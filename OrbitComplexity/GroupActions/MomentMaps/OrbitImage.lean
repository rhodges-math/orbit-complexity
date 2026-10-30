import OrbitComplexity.GroupActions.Tori.ProjectiveOrbitRank
import OrbitComplexity.GroupActions.MomentMaps.ExponentialImage
import OrbitComplexity.GroupActions.MomentMaps.PositivePoints
import OrbitComplexity.GroupActions.MomentMaps.ClosureEquations
import OrbitComplexity.GroupActions.MomentMaps.FaceInteriors
import OrbitComplexity.GroupActions.MomentMaps.Degenerations
import Batteries.Tactic.Lint

/-! # Moment images of projective torus orbits

The moment image of the algebraic torus orbit of a complex projective point
is the intrinsic interior of its supported weight polytope. Positive character
points realize all points of that intrinsic interior. Faces of the Zariski
orbit closure give its full supported-polytope moment image.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Multiplicative TauCeti WithConv

namespace GroupActions

noncomputable section

section Coordinates

variable {I J : Type} [iFintype : Fintype I] [iDecEq : DecidableEq I] [jFinite : Finite J]

private theorem orbit_coordinates (χ : I → J →₀ ℤ)
    (g : WithConv (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)) →ₐ[ℂ] ℂ))
    (v : I → ℂ) (hv : v ≠ 0) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
      I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    momentMap (fun i j => (χ i j : ℝ))
      (projectivePointsEquiv.symm
        (affineGroupPointsMulEquiv ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) g •
          projectiveVectorPoint v hv)) =
      Finset.univ.centerMass
        (fun i => Complex.normSq (v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1)))
        (fun i j => (χ i j : ℝ)) := by
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
    I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  have hs := @projective_weights_smul ℂ I J inferInstance iFintype iDecEq jFinite
    inferInstance χ g v hv
  rw [hs, ← projectivePointsEquiv_mk, Equiv.symm_apply_apply, momentMap_mk]



/-- The supported weight polytope is unchanged by the algebraic torus action. -/
theorem projective_weightPolytope_smul (χ : I → J →₀ ℤ)
    (t : (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points)
    (x : (projectiveVariety ℂ I).points) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
      I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    weightPolytope (fun i j => (χ i j : ℝ)) (projectivePointsEquiv.symm (t • x)) =
      weightPolytope (fun i j => (χ i j : ℝ)) (projectivePointsEquiv.symm x) := by
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
    I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  obtain ⟨p, rfl⟩ := (projectivePointsEquiv (K := ℂ) (ι := I)).surjective x
  refine Projectivization.ind ?_ p
  intro v hv
  simp only [projectivePointsEquiv_mk]
  obtain ⟨g, rfl⟩ :=
    (affineGroupPointsMulEquiv ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).surjective t
  have hs := @projective_weights_smul ℂ I J inferInstance iFintype iDecEq jFinite
    inferInstance χ g v hv
  rw [hs, ← projectivePointsEquiv_mk, Equiv.symm_apply_apply,
    ← projectivePointsEquiv_mk, Equiv.symm_apply_apply, weightPolytope_mk,
    weightPolytope_mk]
  have hchar (i : I) : g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1) ≠ 0 := by
    rw [← DiagonalizableGroup.charOfPoint_apply_coe]
    exact Units.ne_zero _
  have hsupport : Function.support
      (fun i => v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1)) =
        Function.support v := by
    ext i
    change v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1) ≠ 0 ↔ v i ≠ 0
    exact ⟨fun h => (mul_ne_zero_iff.mp h).1, fun h => mul_ne_zero h (hchar i)⟩
  rw [hsupport]

end Coordinates

/-- The algebraic torus orbit has exactly the intrinsic-interior moment image. -/
theorem projective_orbit_moment_image {I J : Type} [iFintype : Fintype I]
    [iDecEq : DecidableEq I] [jFintype : Fintype J] (χ : I → J →₀ ℤ)
    (v : I → ℂ) (hv : v ≠ 0) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
      I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    Set.range (fun t : (affineVariety ℂ
        (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points =>
      momentMap (fun i j => (χ i j : ℝ))
        (projectivePointsEquiv.symm (t • projectiveVectorPoint v hv))) =
      intrinsicInterior ℝ (weightPolytope (fun i j => (χ i j : ℝ))
        (Projectivization.mk ℂ v hv)) := by
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
    I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  ext q
  constructor
  · rintro ⟨t, rfl⟩
    change momentMap (fun i j => (χ i j : ℝ))
      (projectivePointsEquiv.symm (t • projectiveVectorPoint v hv)) ∈ _
    have hmember := momentMap_mem_intrinsicInterior (fun i j => (χ i j : ℝ))
      (projectivePointsEquiv.symm (t • projectiveVectorPoint v hv))
    rw [@projective_weightPolytope_smul I J iFintype iDecEq inferInstance
      χ t (projectiveVectorPoint v hv)] at hmember
    simpa only [← projectivePointsEquiv_mk, Equiv.symm_apply_apply] using hmember
  · intro hq
    have hexp := @exists_momentMap_exp_eq I (J → ℝ) iFintype
      inferInstance inferInstance inferInstance (fun i j => (χ i j : ℝ)) v hv q hq
    obtain ⟨ℓ, hnonzero, _, _, hmoment⟩ := hexp
    let f : (J →₀ ℤ) →+ ℝ :=
      { toFun := fun m => ℓ (fun j => (m j : ℝ))
        map_zero' := by
          simp only [Finsupp.zero_apply, Int.cast_zero]
          exact map_zero ℓ
        map_add' := by
          intro a b
          have hadd : (fun j => ((a + b) j : ℝ)) =
              (fun j => (a j : ℝ)) + (fun j => (b j : ℝ)) := by
            funext j
            simp only [Finsupp.add_apply, Int.cast_add, Pi.add_apply]
          change ℓ (fun j => ((a + b) j : ℝ)) = _
          rw [hadd, map_add] }
    let g := WithConv.toConv (DiagonalizableGroup.point (R := ℂ) (positiveCharacter f))
    have hg (i : I) : g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1) =
        (Real.exp (ℓ (fun j => (χ i j : ℝ)) / 2) : ℂ) := by
      change DiagonalizableGroup.point (positiveCharacter f)
        (MonoidAlgebra.single (ofAdd (χ i)) 1) = _
      rw [DiagonalizableGroup.point_single_one, positiveCharacter_apply]
      rfl
    refine ⟨affineGroupPointsMulEquiv ℂ
      (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) g, ?_⟩
    change momentMap (fun i j => (χ i j : ℝ))
      (projectivePointsEquiv.symm
        (affineGroupPointsMulEquiv ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) g •
          projectiveVectorPoint v hv)) = q
    rw [@orbit_coordinates I J iFintype iDecEq inferInstance χ g v hv]
    simp only [hg]
    simpa only [momentMap_mk] using hmoment


/-- The moment image of an algebraic torus orbit closure is its weight polytope. -/
theorem projective_closure_moment_image {I J : Type} [iFintype : Fintype I]
    [iDecEq : DecidableEq I] [jFintype : Fintype J] (χ : I → J →₀ ℤ)
    (v : I → ℂ) (hv : v ≠ 0) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
      I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    Set.range (fun p : {p : Projectivization ℂ (I → ℂ) //
        (projectiveVariety ℂ I).pointMap (projectivePointsEquiv p) ∈
          orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
            (projectiveVariety ℂ I) (projectiveVectorPoint v hv)} =>
      momentMap (fun i j => (χ i j : ℝ)) p.val) =
        weightPolytope (fun i j => (χ i j : ℝ)) (Projectivization.mk ℂ v hv) := by
  classical
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
    I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  ext q
  constructor
  · rintro ⟨⟨p, hp⟩, rfl⟩
    change momentMap (fun i j => (χ i j : ℝ)) p ∈ _
    have hpoint : projectiveVectorPoint p.rep p.rep_nonzero = projectivePointsEquiv p := by
      rw [← projectivePointsEquiv_mk, Projectivization.mk_rep]
    have hp' : (projectiveVariety ℂ I).pointMap
        (projectiveVectorPoint p.rep p.rep_nonzero) ∈
      orbitClosure (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
        (projectiveVariety ℂ I) (projectiveVectorPoint v hv) := by
      rwa [hpoint]
    have hface := @projective_closure_face I J iFintype iDecEq inferInstance
      χ v hv p.rep p.rep_nonzero hp'
    have hexposed : IsExposed ℝ
        (weightPolytope (fun i j => (χ i j : ℝ)) (Projectivization.mk ℂ v hv))
        (weightPolytope (fun i j => (χ i j : ℝ)) p) := by
      simpa only [Projectivization.mk_rep] using hface.2.1
    exact hexposed.subset (momentMap_mem_weightPolytope (fun i j => (χ i j : ℝ)) p)
  · intro hq
    have hq' : q ∈ convexHull ℝ
        (Set.range (fun i : Function.support v => fun j => (χ i.val j : ℝ))) := by
      simpa only [weightPolytope_mk, Set.image_eq_range] using hq
    have hfaces := @exists_exposed_intrinsicInterior (Function.support v) (J → ℝ)
      inferInstance inferInstance inferInstance inferInstance
      (fun i j => (χ i.val j : ℝ)) q hq'
    obtain ⟨F, hne, hF, hqF⟩ := hfaces
    have hF' : IsExposed ℝ
        (convexHull ℝ ((fun i j => (χ i j : ℝ)) '' Function.support v)) F := by
      simpa only [Set.image_eq_range] using hF
    let y := fun i => @ite ℂ ((fun j => (χ i j : ℝ)) ∈ F)
      (Classical.propDecidable _) (v i) 0
    have hpoint := @exposed_face_point ℂ inferInstance inferInstance I J
      iFintype iDecEq inferInstance χ v hv F hF' hne
    obtain ⟨hy, hclosed, hhull⟩ := hpoint
    change convexHull ℝ ((fun i j => (χ i j : ℝ)) '' Function.support y) = F at hhull
    have hqY : q ∈ intrinsicInterior ℝ
        (weightPolytope (fun i j => (χ i j : ℝ)) (Projectivization.mk ℂ y hy)) := by
      rw [weightPolytope_mk, hhull]
      exact hqF
    have himage := @projective_orbit_moment_image I J iFintype iDecEq jFintype χ y hy
    rw [← himage] at hqY
    obtain ⟨t, ht⟩ := hqY
    refine ⟨⟨projectivePointsEquiv.symm (t • projectiveVectorPoint y hy), ?_⟩, ?_⟩
    · have htranslate := @orbitClosure_smul_mem ℂ inferInstance
        (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))))
        (projectiveVariety ℂ I) inferInstance inferInstance
        (projectiveVectorPoint v hv) (projectiveVectorPoint y hy) t hclosed
      simpa only [Equiv.apply_symm_apply] using htranslate
    · change momentMap (fun i j => (χ i j : ℝ))
        (projectivePointsEquiv.symm (t • projectiveVectorPoint y hy)) = q
      exact ht

end

/-- A projective point with a singleton supported weight polytope is fixed by the torus. -/
theorem projective_fixed_of_singleton {I J : Type} [iFintype : Fintype I]
    [iDecEq : DecidableEq I] [jFinite : Finite J] (χ : I → J →₀ ℤ)
    (x : (projectiveVariety ℂ I).points) (q : J → ℝ)
    (hx : weightPolytope (fun i j => (χ i j : ℝ))
      (projectivePointsEquiv.symm x) = {q}) :
    letI : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
      Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
    letI := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
      I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (Pi.basisFun ℂ I)
    ∀ t : (affineVariety ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).points,
      t • x = x := by
  let : Comodule ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ))) (I → ℂ) :=
    Comodule.ofWeights (Pi.basisFun ℂ I) (fun i => ofAdd (χ i))
  let := @comoduleProjectiveAction ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))
    I (I → ℂ) inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Pi.basisFun ℂ I)
  obtain ⟨p, rfl⟩ := (projectivePointsEquiv (K := ℂ) (ι := I)).surjective x
  induction p using Projectivization.ind with
  | _ v hv =>
    have hx' : convexHull ℝ ((fun i j => (χ i j : ℝ)) '' Function.support v) = {q} := by
      simpa only [Equiv.symm_apply_apply, weightPolytope_mk] using hx
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
    have hweight (i : I) (hi : v i ≠ 0) : (fun j => (χ i j : ℝ)) = q := by
      have hm := subset_convexHull ℝ
        ((fun i j => (χ i j : ℝ)) '' Function.support v)
        (Set.mem_image_of_mem (fun i j => (χ i j : ℝ)) hi)
      rw [hx'] at hm
      exact Set.mem_singleton_iff.mp hm
    have hχ (i : I) (hi : v i ≠ 0) : χ i = χ i₀ := by
      ext j
      exact Int.cast_injective (congrFun ((hweight i hi).trans (hweight i₀ hi₀).symm) j)
    intro t
    obtain ⟨g, rfl⟩ :=
      (affineGroupPointsMulEquiv ℂ (MonoidAlgebra ℂ (Multiplicative (J →₀ ℤ)))).surjective t
    simp only [projectivePointsEquiv_mk]
    have hs := @projective_weights_smul ℂ I J inferInstance iFintype iDecEq jFinite
      inferInstance χ g v hv
    rw [hs]
    let a : ℂˣ := DiagonalizableGroup.charOfPoint g.ofConv (ofAdd (χ i₀))
    have hscale : (fun i => v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1)) =
        (a : ℂ) • v := by
      funext i
      change v i * g.ofConv (MonoidAlgebra.single (ofAdd (χ i)) 1) = (a : ℂ) * v i
      by_cases hi : v i = 0
      · simp only [hi, zero_mul, mul_zero]
      · rw [hχ i hi, ← DiagonalizableGroup.charOfPoint_apply_coe]
        exact mul_comm _ _
    calc
      _ = projectiveVectorPoint ((a : ℂ) • v) (smul_ne_zero a.ne_zero hv) := by
        congr 1
      _ = _ := projectiveVectorPoint_scale v hv a


end GroupActions
