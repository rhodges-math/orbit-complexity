import OrbitComplexity.SchubertGeometry.LineBundles.Modules.OverlapAmbient
import OrbitComplexity.SchubertGeometry.LineBundles.Modules.RankoneFrames
import OrbitComplexity.SchubertGeometry.Normality.Models.RankoneSections
import OrbitComplexity.ReductiveGroups.Groups.GaCoordinates.GaProductCoordinates

/-! # The rank-one frames and their regular Borel transition -/

noncomputable section
namespace SchubertGeometry.ProjectiveLine
open ReductiveGroups GroupActions TauCeti CategoryTheory AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K)

private abbrev coordinate (K : Type u) [Field K] :=
  MonoidAlgebra K (Multiplicative ℤ)
omit [IsAlgClosed K] [CharZero K] in
private theorem gmReduced : IsReduced (coordinate K) := by infer_instance
omit [IsAlgClosed K] [CharZero K] in
private theorem gmFinite : Algebra.FiniteType K (coordinate K) := by infer_instance
omit [CharZero K] in
private theorem borelReduced : IsReduced G.borelAlgebra := by
  let : Algebra.Smooth K G.borelAlgebra := G.borel_smooth
  exact isReduced_of_smooth K G.borelAlgebra
attribute [local instance] gmReduced gmFinite borelReduced

/-- The multiplicative coordinate to an integral power, regarded as an additive parameter. -/
def multiplicativeParameter (n : ℤ) :
    (affineVariety K (coordinate K)).toOver ⟶ (additiveVariety K).toOver :=
  affineMorphism (SymmetricAlgebra.lift (LinearMap.toSpanSingleton K _
    (MonoidAlgebra.single (Multiplicative.ofAdd n) 1)))

/-- The coordinate Borel factor is a regular morphism on the punctured chart. -/
def simpleOverlapMorphism (i : G.rootBase.support) :
    (affineVariety K (coordinate K)).toOver ⟶ (borelVariety G).toOver :=
  affineMorphism (simpleOverlapCoordinate G i)

private def gmPoint (a : Kˣ) : WithConv (coordinate K →ₐ[K] K) :=
  (DiagonalizableGroup.pointsMulEquiv (R := K)).symm (zpowersHom Kˣ a)

private def gmVarPoint (a : Kˣ) : (affineVariety K (coordinate K)).points :=
  affinePointsEquiv (gmPoint a).ofConv

omit [IsAlgClosed K] [CharZero K] in
private theorem gmPoint_single (a : Kˣ) (n : ℤ) :
    (gmPoint a).ofConv (MonoidAlgebra.single (Multiplicative.ofAdd n) 1) =
      ((a ^ n : Kˣ) : K) := by
  have h := DiagonalizableGroup.charOfPoint_apply_coe
    (gmPoint a).ofConv (Multiplicative.ofAdd n)
  change (DiagonalizableGroup.pointsMulEquiv (gmPoint a)
    (Multiplicative.ofAdd n) : K) = _ at h
  rw [gmPoint, MulEquiv.apply_symm_apply, zpowersHom_apply, toAdd_ofAdd] at h
  exact h.symm

omit [IsAlgClosed K] [CharZero K] in
private theorem parameter_points (a : Kˣ) (n : ℤ) :
    Variety.mapPoints (multiplicativeParameter (K := K) n)
      (gmVarPoint a) =
        additivePointsEquiv K ((a ^ n : Kˣ) : K) := by
  have h : (gmPoint a).ofConv.comp (SymmetricAlgebra.lift
      (LinearMap.toSpanSingleton K _
        (MonoidAlgebra.single (Multiplicative.ofAdd n) 1))) =
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (Multiplicative.ofAdd ((a ^ n : Kˣ) : K))).ofConv := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change (gmPoint a).ofConv ((SymmetricAlgebra.lift
      (LinearMap.toSpanSingleton K _ (MonoidAlgebra.single (Multiplicative.ofAdd n) 1)))
        (SymmetricAlgebra.ι K K x)) =
      ((AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
        (Multiplicative.ofAdd ((a ^ n : Kˣ) : K))).ofConv (SymmetricAlgebra.ι K K x)
    have hι : SymmetricAlgebra.ι K K x = x • SymmetricAlgebra.ι K K 1 := by
      simpa only [smul_eq_mul, mul_one] using
        (map_smul (SymmetricAlgebra.ι K K) x (1 : K))
    simp only [hι, map_smul, SymmetricAlgebra.lift_ι_apply,
      LinearMap.toSpanSingleton_apply, one_smul, gmPoint_single,
      AdditiveGroup.gaPointsMulEquiv_symm_apply_ι, toAdd_ofAdd]

  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (gmPoint a).ofConv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (SymmetricAlgebra.lift
      (LinearMap.toSpanSingleton K _
        (MonoidAlgebra.single (Multiplicative.ofAdd n) 1))).toRingHom) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : SymmetricAlgebra K K →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) h

private theorem overlap_points (i : G.rootBase.support) (a : Kˣ) :
    Variety.mapPoints (simpleOverlapMorphism G i ≫ borelInclusion G)
      (gmVarPoint a) =
      reductivePointsEquiv G (Coroot.simpleCorootPoint G i a *
        gaParameterPoint (G.simpleRootMap i) (-↑(a⁻¹) : K)) := by
  have hc : AlgHom.mapValue (gmPoint a).ofConv
      (toConv (Coroot.simpleCorootMap G i).toAlgHom) =
        Coroot.simpleCorootPoint G i a := by
    rw [Coroot.simpleCorootPoint_map]
    rfl
  have he := congrArg (fun f : G.coordinateAlgebra →ₐ[K] coordinate K =>
    (gmPoint a).ofConv.comp f) (simpleOverlapCoordinate_ambient G i)
  have hm := map_mul (AlgHom.mapValue (gmPoint a).ofConv)
    (toConv (Coroot.simpleCorootMap G i).toAlgHom)
    (gaParameterPoint (G.simpleRootMap i)
      (-MonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1 : coordinate K))
  have ht : (gmPoint a).ofConv
      (-MonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1) = (-↑(a⁻¹) : K) := by
    calc
      _ = -(gmPoint a).ofConv (MonoidAlgebra.single (Multiplicative.ofAdd (-1)) 1) :=
        map_neg _ _
      _ = _ := by rw [gmPoint_single, zpow_neg_one]
  rw [hc, gaParameterPoint_mapValue, ht] at hm
  let qB : G.coordinateAlgebra →ₐ[K] G.borelAlgebra :=
    (CommHopfAlgCat.mkQuotient G.coordinateAlgebra.obj G.borelIdeal).hom.toAlgHom
  have hf : (simpleOverlapMorphism G i ≫ borelInclusion G).left =
      Spec.map (CommRingCat.ofHom ((simpleOverlapCoordinate G i).comp qB).toRingHom) := by
    exact (Spec.map_comp (CommRingCat.ofHom qB.toRingHom)
      (CommRingCat.ofHom (simpleOverlapCoordinate G i).toRingHom)).symm
  have hcoord : (gmPoint a).ofConv.comp ((simpleOverlapCoordinate G i).comp qB) =
      (Coroot.simpleCorootPoint G i a *
        gaParameterPoint (G.simpleRootMap i) (-↑(a⁻¹) : K)).ofConv :=
    he.trans (congrArg WithConv.ofConv hm)
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (gmPoint a).ofConv.toRingHom) ≫
      (simpleOverlapMorphism G i ≫ borelInclusion G).left = _
  rw [hf]
  exact (Spec.map_comp
    (CommRingCat.ofHom ((simpleOverlapCoordinate G i).comp qB).toRingHom)
    (CommRingCat.ofHom (gmPoint a).ofConv.toRingHom)).symm.trans
      (congrArg (fun f : G.coordinateAlgebra →ₐ[K] K =>
        Spec.map (CommRingCat.ofHom f.toRingHom)) hcoord)

omit [IsAlgClosed K] [CharZero K] in
private theorem mapPoints_mul {X H : Variety K} [GrpObj H.toOver]
    (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    Variety.mapPoints (f * g) x = Variety.mapPoints f x * Variety.mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

/-- On the overlap the positive frame is the negative frame times the Borel factor. -/
theorem simpleFrames_transition (i : G.rootBase.support) :
    multiplicativeParameter (K := K) 1 ≫ simplePositiveSection G i =
      (multiplicativeParameter (K := K) (-1) ≫ simpleNegativeSection G i) *
        (simpleOverlapMorphism G i ≫ borelInclusion G) := by
  apply Variety.mapPoints_injective
    (X := affineVariety K (coordinate K)) (Y := reductiveVariety G)
  funext p
  obtain ⟨q, rfl⟩ := (affinePointsEquiv (K := K) (R := coordinate K)).surjective p
  let a : Kˣ := (zpowersHom Kˣ).symm
    (DiagonalizableGroup.pointsMulEquiv (toConv q))
  have hq : gmPoint a = toConv q := by
    unfold gmPoint a
    rw [Equiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  have hq' : q = (gmPoint a).ofConv := congrArg WithConv.ofConv hq.symm
  rw [hq']
  change Variety.mapPoints (multiplicativeParameter (K := K) 1 ≫
    simplePositiveSection G i) (gmVarPoint a) =
      Variety.mapPoints ((multiplicativeParameter (K := K) (-1) ≫
        simpleNegativeSection G i) * (simpleOverlapMorphism G i ≫ borelInclusion G))
          (gmVarPoint a)
  have ho := overlap_points G i a
  rw [Variety.mapPoints_comp] at ho
  rw [mapPoints_mul]
  simp only [Variety.mapPoints_comp]
  rw [parameter_points, parameter_points, zpow_one, zpow_neg_one, ho]
  simp only [simplePositiveSection, simpleNegativeSection, Variety.mapPoints_comp]
  rw [gaMorphism_points, gaMorphism_points, rightTranslation_points]
  change reductivePointsMulEquiv G _ * reductivePointsMulEquiv G _ =
    reductivePointsMulEquiv G _ * reductivePointsMulEquiv G _
  rw [← (reductivePointsMulEquiv G).map_mul, ← (reductivePointsMulEquiv G).map_mul]
  apply congrArg (reductivePointsEquiv G)
  exact (simpleFrame_overlap G i a).symm

end SchubertGeometry.ProjectiveLine
