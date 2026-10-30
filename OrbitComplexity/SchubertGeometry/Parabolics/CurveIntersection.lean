import OrbitComplexity.SchubertGeometry.Parabolics.SimpleCurve
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaPolynomialCoordinate
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Simple-curve intersections in affine charts

An ascending simple-curve intersection is the entire curve or embeds in its negative affine
chart with a nilpotent coordinate and a rational section.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
universe u

private def additiveCoordinate (K : Type u) [Field K] :
    Γ((additiveVariety K).scheme, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (SymmetricAlgebra K K))).inv
    (SymmetricAlgebra.ι K K 1)

private theorem zero_not_basicOpen (K : Type u) [Field K] :
    (additiveVariety K).pointMap (additivePointsEquiv K 0) ∉
      (additiveVariety K).scheme.basicOpen (additiveCoordinate K) := by
  have hpre : (additivePointsEquiv K 0).val ⁻¹ᵁ
      (additiveVariety K).scheme.basicOpen (additiveCoordinate K) = ⊥ := by
    change Spec.map (CommRingCat.ofHom
        ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
          (Multiplicative.ofAdd 0)).ofConv.toRingHom) ⁻¹ᵁ
      (Spec (CommRingCat.of (SymmetricAlgebra K K))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of (SymmetricAlgebra K K))).inv
          (SymmetricAlgebra.ι K K 1)) = ⊥
    rw [basicOpen_eq_of_affine, SpecMap_preimage_basicOpen]
    have hz :
        ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
          (Multiplicative.ofAdd 0)).ofConv (SymmetricAlgebra.ι K K 1) = 0 := by
      rw [← gaPolynomialEquiv_eval_point K 0, gaPolynomialEquiv_generator, Polynomial.eval_X]
    have hb : PrimeSpectrum.basicOpen
        (((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
          (Multiplicative.ofAdd 0)).ofConv (SymmetricAlgebra.ι K K 1)) =
        (⊥ : TopologicalSpace.Opens (PrimeSpectrum K)) := by
      rw [hz]
      exact PrimeSpectrum.basicOpen_zero
    exact hb
  intro hx
  have hm : IsLocalRing.closedPoint K ∈
      (additivePointsEquiv K 0).val ⁻¹ᵁ
        (additiveVariety K).scheme.basicOpen (additiveCoordinate K) := hx
  rw [hpre] at hm
  exact hm

private theorem coordinate_nilpotent {K : Type u} [Field K] {X : Scheme.{u}}
    [CompactSpace X] (f : X ⟶ (additiveVariety K).scheme)
    (hz : ∀ x : X, f x = (additiveVariety K).pointMap (additivePointsEquiv K 0)) :
    ∃ N : ℕ, 0 < N ∧ (f.appTop (additiveCoordinate K)) ^ N = 0 := by
  have hb : X.basicOpen (f.appTop (additiveCoordinate K)) = ⊥ := by
    rw [← f.preimage_basicOpen_top]
    apply TopologicalSpace.Opens.ext
    ext x
    change f x ∈ (additiveVariety K).scheme.basicOpen (additiveCoordinate K) ↔ False
    rw [hz x]
    exact iff_false_intro (zero_not_basicOpen K)
  obtain ⟨n, hn⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot (X := X) _).mpr hb
  exact ⟨n + 1, Nat.zero_lt_succ n, by rw [pow_succ, hn, zero_mul]⟩

private theorem closed_chart_lift {X Y Z : Scheme.{u}} (f : X ⟶ Z) (j : Y ⟶ Z)
    [IsClosedImmersion f] [IsOpenImmersion j] [IsAffine Y]
    (hrange : Set.range f ⊆ Set.range j) :
    ∃ c : X ⟶ Y, IsClosedImmersion c ∧ IsAffine X ∧ c ≫ j = f := by
  let c := IsOpenImmersion.lift j f hrange
  have hc : IsPullback c (𝟙 X) j f := IsOpenImmersion.isPullback_lift_id f j hrange
  let : IsClosedImmersion c := MorphismProperty.of_isPullback hc.flip inferInstance
  have ha : IsAffine X := isAffine_of_isAffineHom c
  exact ⟨c, inferInstance, ha, IsOpenImmersion.lift_fac j f hrange⟩


variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

private theorem curve_zero (w : G.weylGroup) (i : G.rootBase.support) :
    Variety.mapPoints (simpleNegativeChart G i ≫ simpleSchubertCurve G w i)
      (additivePointsEquiv K 0) = weylFlagPoint G w := by
  rw [simpleSchubertCurve, ← Category.assoc, Variety.mapPoints_comp,
    simpleNegativeChart_points, gaParameterPoint_zero,
    Variety.mapPoints_translateMorphism, flagVarietyAction_points,
    ← flagProjection_smul, mul_one]
  rfl

private theorem intersection_section (w v : G.weylGroup) (i : G.rootBase.support)
    (hwv : WeylBruhatLE G.rootBase w v) :
    let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
    let I := pullback (simpleSchubertCurve G w i).left (schubertInclusion G v).left
    let f : I ⟶ Y.scheme :=
      pullback.fst (simpleSchubertCurve G w i).left (schubertInclusion G v).left
    ∃ σ : Spec (CommRingCat.of K) ⟶ I, σ ≫ (f ≫ Y.toSpec) = 𝟙 _ := by
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let I := pullback (simpleSchubertCurve G w i).left (schubertInclusion G v).left
  let f : I ⟶ Y.scheme :=
    pullback.fst (simpleSchubertCurve G w i).left (schubertInclusion G v).left
  let z : Y.points := Variety.mapPoints (simpleNegativeChart G i) (additivePointsEquiv K 0)
  have hz : Variety.mapPoints (simpleSchubertCurve G w i) z = weylFlagPoint G w := by
    change Variety.mapPoints (simpleSchubertCurve G w i)
      (Variety.mapPoints (simpleNegativeChart G i) (additivePointsEquiv K 0)) = _
    rw [← Variety.mapPoints_comp]
    exact curve_zero G w i
  obtain ⟨q, hq⟩ := (weylFlag_mem_schubert_iff G w v).mpr hwv
  have hcomm : z.val ≫ (simpleSchubertCurve G w i).left =
      q.val ≫ (schubertInclusion G v).left :=
    (congrArg Subtype.val hz).trans (congrArg Subtype.val hq).symm
  let σ := pullback.lift z.val q.val hcomm
  have hf : σ ≫ f = z.val := pullback.lift_fst z.val q.val hcomm
  refine ⟨σ, ?_⟩
  exact (Category.assoc σ f Y.toSpec).symm.trans
    ((congrArg (fun a => a ≫ Y.toSpec) hf).trans z.property)

/-- A simple-curve intersection is the whole curve or has finite nilpotent chart data. -/
theorem simpleCurve_finite_cases (w v : G.weylGroup) (i : G.rootBase.support)
    (hw : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i.val))
    (hwv : WeylBruhatLE G.rootBase w v) :
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let I := pullback (simpleSchubertCurve G w i).left (schubertInclusion G v).left
  let f : I ⟶ Y.scheme :=
    pullback.fst (simpleSchubertCurve G w i).left (schubertInclusion G v).left
  let b := f ≫ Y.toSpec
  let X := Over.mk b
  let inclusion : X ⟶ Y.toOver := Over.homMk f rfl
  (∃ e : X ≅ Y.toOver, e.hom = inclusion) ∨
    ∃ c : X ⟶ (additiveVariety K).toOver,
      IsClosedImmersion c.left ∧ IsAffine I ∧
      c ≫ simpleNegativeChart G i = inclusion ∧
      (∃ N : ℕ, 0 < N ∧
        (c.left.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (SymmetricAlgebra K K))).inv
            (SymmetricAlgebra.ι K K 1))) ^ N = 0) ∧
      ∃ σ : Spec (CommRingCat.of K) ⟶ I, σ ≫ b = 𝟙 _ := by
  let Y := schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)
  let I := pullback (simpleSchubertCurve G w i).left (schubertInclusion G v).left
  let f : I ⟶ Y.scheme :=
    pullback.fst (simpleSchubertCurve G w i).left (schubertInclusion G v).left
  let b := f ≫ Y.toSpec
  let X := Over.mk b
  let inclusion : X ⟶ Y.toOver := Over.homMk f rfl
  let a0 := additivePointsEquiv K 0
  let z : Y.points := Variety.mapPoints (simpleNegativeChart G i) a0
  have hr : Set.range f = (simpleSchubertCurve G w i).left ⁻¹'
      Set.range (schubertInclusion G v).left := Scheme.Pullback.range_fst _ _
  have hcases : Set.range f = Set.univ ∨ Set.range f = {Y.pointMap z} := by
    rcases simpleCurve_image_cases G w i v hw hwv with h | h
    · exact Or.inl (hr.trans h)
    · exact Or.inr (hr.trans h)
  rcases hcases with hfull | hpoint
  · let : Surjective f := ⟨Set.range_eq_univ.mp hfull⟩
    let : IsIso f := isIso_of_isClosedImmersion_of_surjective f
    let : IsIso ((Over.forget (Spec (CommRingCat.of K))).map inclusion) :=
      inferInstanceAs (IsIso f)
    let : IsIso inclusion := isIso_of_reflects_iso inclusion (Over.forget _)
    exact Or.inl ⟨asIso inclusion, rfl⟩
  · have hzimage (p : I) : f p = Y.pointMap z := by
      have hm : f p ∈ Set.range f := ⟨p, rfl⟩
      rw [hpoint] at hm
      exact hm
    have hrange : Set.range f ⊆ Set.range (simpleNegativeChart G i).left := by
      rintro _ ⟨p, rfl⟩
      refine ⟨(additiveVariety K).pointMap a0, ?_⟩
      exact (Variety.pointMap_mapPoints (simpleNegativeChart G i) a0).symm.trans (hzimage p).symm
    let : IsAffine (additiveVariety K).toOver.left := by
      change IsAffine (Spec (CommRingCat.of (SymmetricAlgebra K K)))
      infer_instance
    obtain ⟨c, hc, ha, hcf⟩ := closed_chart_lift f (simpleNegativeChart G i).left hrange
    let : IsClosedImmersion c := hc
    let : IsAffine I := ha
    have hczero (p : I) : c p = (additiveVariety K).pointMap a0 := by
      apply (simpleNegativeChart G i).left.isEmbedding.injective
      have hp := congrArg (fun a => a p) hcf
      change (simpleNegativeChart G i).left (c p) = f p at hp
      exact hp.trans ((hzimage p).trans
        (Variety.pointMap_mapPoints (simpleNegativeChart G i) a0))
    have hbase : c ≫ (additiveVariety K).toSpec = b :=
      (congrArg (fun a => c ≫ a) (simpleNegativeChart G i).w.symm).trans
        ((Category.assoc c (simpleNegativeChart G i).left Y.toSpec).symm.trans
          (congrArg (fun a => a ≫ Y.toSpec) hcf))
    let cOver : X ⟶ (additiveVariety K).toOver := Over.homMk c hbase
    have hfactor : cOver ≫ simpleNegativeChart G i = inclusion := by
      apply Over.OverMorphism.ext
      exact hcf
    obtain ⟨N, hN, hpow⟩ := coordinate_nilpotent c hczero
    obtain ⟨σ, hσ⟩ := intersection_section G w v i hwv
    exact Or.inr ⟨cOver, hc, ha, hfactor, ⟨N, hN, hpow⟩, σ, hσ⟩

end SchubertGeometry
