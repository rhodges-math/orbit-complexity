import OrbitComplexity.GroupActions.Varieties.CoordinateCharts
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Inversion of a punctured additive coordinate

The nonzero-parameter open of the additive group has a regular inversion isomorphism.
Its pullback on the localized coordinate algebra interchanges the generator and its inverse.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section
universe u
namespace GroupActions
variable (K : Type u) [Field K]

private abbrev additiveGenerator := SymmetricAlgebra.ι K K 1
private abbrev additiveLocalization := Localization.Away (additiveGenerator K)

private def inverseCoordinateMap : SymmetricAlgebra K K →ₐ[K] additiveLocalization K :=
  (Polynomial.aeval (IsLocalization.Away.invSelf (additiveGenerator K))).comp
    (ReductiveGroups.gaPolynomialEquiv K).toAlgHom

private theorem inverseCoordinate_generator :
    inverseCoordinateMap K (additiveGenerator K) =
      IsLocalization.Away.invSelf (additiveGenerator K) := by
  simp [inverseCoordinateMap, additiveGenerator]

private theorem invSelf_isUnit :
    IsUnit (IsLocalization.Away.invSelf (additiveGenerator K) : additiveLocalization K) :=
  isUnit_iff_exists_inv.mpr ⟨algebraMap _ _ (additiveGenerator K), by
    rw [mul_comm, IsLocalization.Away.mul_invSelf]⟩

private theorem inverseCoordinate_unit :
    IsUnit (inverseCoordinateMap K (additiveGenerator K)) := by
  rw [inverseCoordinate_generator]
  exact invSelf_isUnit K

private def inverseLocalization : additiveLocalization K →ₐ[K] additiveLocalization K :=
  IsLocalization.Away.liftAlgHom (f := inverseCoordinateMap K)
    (additiveGenerator K) (inverseCoordinate_unit K)

private theorem inverseLocalization_generator :
    inverseLocalization K (algebraMap _ _ (additiveGenerator K)) =
      IsLocalization.Away.invSelf (additiveGenerator K) := by
  rw [inverseLocalization, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  exact inverseCoordinate_generator K

private theorem inverseLocalization_invSelf :
    inverseLocalization K (IsLocalization.Away.invSelf (additiveGenerator K)) =
      algebraMap _ _ (additiveGenerator K) := by
  apply (invSelf_isUnit K).mul_right_inj.mp
  have h := congrArg (inverseLocalization K)
    (IsLocalization.Away.mul_invSelf (S := additiveLocalization K) (additiveGenerator K))
  rw [map_mul, map_one, inverseLocalization_generator] at h
  exact h.trans (by rw [mul_comm, IsLocalization.Away.mul_invSelf])

private theorem inverseLocalization_twice :
    (inverseLocalization K).comp (inverseLocalization K) = AlgHom.id K _ := by
  let a := IsScalarTower.toAlgHom K (SymmetricAlgebra K K) (additiveLocalization K)
  have h : ((inverseLocalization K).comp (inverseLocalization K)).comp a = a := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    have hx : SymmetricAlgebra.ι K K x = x • additiveGenerator K := by
      simpa only [smul_eq_mul, mul_one] using
        (map_smul (SymmetricAlgebra.ι K K) x (1 : K))
    change inverseLocalization K (inverseLocalization K
      (a (SymmetricAlgebra.ι K K x))) = a (SymmetricAlgebra.ι K K x)
    rw [hx]
    simp only [map_smul]
    exact congrArg (fun y => x • y) (by
      change inverseLocalization K (inverseLocalization K
        (algebraMap _ _ (additiveGenerator K))) = algebraMap _ _ (additiveGenerator K)
      rw [inverseLocalization_generator, inverseLocalization_invSelf])
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (additiveGenerator K))
  exact congrArg AlgHom.toRingHom h

private def inverseLocalizationEquiv : additiveLocalization K ≃ₐ[K] additiveLocalization K :=
  AlgEquiv.ofAlgHom (inverseLocalization K) (inverseLocalization K)
    (inverseLocalization_twice K) (inverseLocalization_twice K)


private instance inverseLocalizationFinite :
    Algebra.FiniteType K (additiveLocalization K) :=
  Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K (SymmetricAlgebra K K))
    (inferInstance : Algebra.FiniteType (SymmetricAlgebra K K) (additiveLocalization K))

private def puncturedLocalizationIso :
    ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver ≅
      (affineVariety K (additiveLocalization K)).toOver :=
  Over.isoMk (basicOpenIsoSpecAway (R := CommRingCat.of (SymmetricAlgebra K K))
    (additiveGenerator K)) (by
      let D : (additiveVariety K).scheme.Opens := additiveNonzero K
      change (basicOpenIsoSpecAway (R := CommRingCat.of (SymmetricAlgebra K K))
        (additiveGenerator K)).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (additiveLocalization K))) =
        D.ι ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (SymmetricAlgebra K K)))
      have ht : Spec.map (CommRingCat.ofHom (algebraMap K (additiveLocalization K))) =
          Spec.map (CommRingCat.ofHom
            (algebraMap (SymmetricAlgebra K K) (additiveLocalization K))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap K (SymmetricAlgebra K K))) := by
        rw [← Spec.map_comp]
        congr 2
      rw [ht, ← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
      rfl)

private theorem puncturedLocalizationIso_comp :
    (puncturedLocalizationIso K).hom ≫
      affineMorphism (IsScalarTower.toAlgHom K (SymmetricAlgebra K K)
        (additiveLocalization K)) = (additiveVariety K).openInclusion (additiveNonzero K) := by
  apply Over.OverMorphism.ext
  exact basicOpenIsoSpecAway_hom_SpecMap
    (R := CommRingCat.of (SymmetricAlgebra K K)) (additiveGenerator K)

/-- Inversion of the nonzero additive parameter is a regular involutive isomorphism. -/
def puncturedAdditiveInvIso :
    ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver ≅
      ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver :=
  puncturedLocalizationIso K ≪≫
    (algSpec (CommRingCat.of K)).mapIso (CommAlgCat.isoMk (inverseLocalizationEquiv K)).op ≪≫
      (puncturedLocalizationIso K).symm

private theorem puncturedAdditiveInvIso_hom : (puncturedAdditiveInvIso K).hom =
    (puncturedLocalizationIso K).hom ≫ affineMorphism (inverseLocalization K) ≫
      (puncturedLocalizationIso K).inv := rfl

private theorem puncturedAdditiveInvIso_comm :
    (puncturedAdditiveInvIso K).hom ≫ (puncturedLocalizationIso K).hom =
      (puncturedLocalizationIso K).hom ≫ affineMorphism (inverseLocalization K) := by
  rw [puncturedAdditiveInvIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem inverse_additive_eval (a : (additiveVariety K).points) :
    affineVarietyPointsEquiv K (SymmetricAlgebra K K) a (additiveGenerator K) =
      (additivePointsEquiv K).symm a := by
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective a
  rw [Equiv.symm_apply_apply]
  let g := ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)).ofConv
  have ht : additivePointsEquiv K t = affinePointsEquiv g := rfl
  rw [ht]
  change (affinePointsEquiv.symm (affinePointsEquiv g)) (additiveGenerator K) = t
  rw [Equiv.symm_apply_apply]
  dsimp only [g, additiveGenerator]
  rw [TauCeti.AdditiveGroup.gaPointsMulEquiv_symm_apply_ι]
  rfl

private theorem parameter_affineMorphism {B : Type u} [CommRing B] [Algebra K B]
    [IsReduced B] [Algebra.FiniteType K B] (f : SymmetricAlgebra K K →ₐ[K] B)
    (x : (affineVariety K B).points) :
    (additivePointsEquiv K).symm (Variety.mapPoints (affineMorphism f) x) =
      affineVarietyPointsEquiv K B x (f (additiveGenerator K)) := by
  rw [← inverse_additive_eval]
  obtain ⟨p, rfl⟩ := (affineVarietyPointsEquiv K B).symm.surjective x
  rw [affineMorphism_points]
  change (affinePointsEquiv.symm (affinePointsEquiv (p.comp f))) (additiveGenerator K) =
    (affinePointsEquiv.symm (affinePointsEquiv p)) (f (additiveGenerator K))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

private theorem parameter_localized
    (x : ((additiveVariety K).openSubvariety (additiveNonzero K)).points) :
    (additivePointsEquiv K).symm
      (Variety.mapPoints ((additiveVariety K).openInclusion (additiveNonzero K)) x) =
    affineVarietyPointsEquiv K (additiveLocalization K)
      (Variety.mapPoints (puncturedLocalizationIso K).hom x)
        (algebraMap _ _ (additiveGenerator K)) := by
  let f : (affineVariety K (additiveLocalization K)).toOver ⟶ (additiveVariety K).toOver :=
    affineMorphism (IsScalarTower.toAlgHom K (SymmetricAlgebra K K) (additiveLocalization K))
  have hp : Variety.mapPoints ((additiveVariety K).openInclusion (additiveNonzero K)) x =
      Variety.mapPoints f (Variety.mapPoints (puncturedLocalizationIso K).hom x) :=
    (congrArg (fun q => Variety.mapPoints q x) (puncturedLocalizationIso_comp K).symm).trans
      (Variety.mapPoints_comp (puncturedLocalizationIso K).hom f x)
  exact (congrArg (additivePointsEquiv K).symm hp).trans
    (parameter_affineMorphism K _ _)

private theorem map_affine_eval {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [IsReduced A] [IsReduced B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B] (f : A →ₐ[K] B)
    (x : (affineVariety K B).points) (a : A) :
    affineVarietyPointsEquiv K A (Variety.mapPoints (affineMorphism f) x) a =
      affineVarietyPointsEquiv K B x (f a) := by
  obtain ⟨p, rfl⟩ := (affineVarietyPointsEquiv K B).symm.surjective x
  rw [affineMorphism_points, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The regular inversion chart replaces the additive parameter by its field inverse. -/
theorem puncturedAdditiveInvIso_points
    (x : ((additiveVariety K).openSubvariety (additiveNonzero K)).points) :
    (additivePointsEquiv K).symm (Variety.mapPoints
      ((additiveVariety K).openInclusion (additiveNonzero K))
        (Variety.mapPoints (puncturedAdditiveInvIso K).hom x)) =
    ((additivePointsEquiv K).symm (Variety.mapPoints
      ((additiveVariety K).openInclusion (additiveNonzero K)) x))⁻¹ := by
  let q := Variety.mapPoints (puncturedLocalizationIso K).hom x
  let p := affineVarietyPointsEquiv K (additiveLocalization K) q
  have hp : Variety.mapPoints (puncturedLocalizationIso K).hom
      (Variety.mapPoints (puncturedAdditiveInvIso K).hom x) =
        Variety.mapPoints (affineMorphism (inverseLocalization K)) q := by
    exact (Variety.mapPoints_comp _ _ _).symm.trans
      ((congrArg (fun f => Variety.mapPoints f x) (puncturedAdditiveInvIso_comm K)).trans
        (Variety.mapPoints_comp _ _ _))
  have hm : p (algebraMap _ _ (additiveGenerator K)) *
      p (IsLocalization.Away.invSelf (additiveGenerator K)) = 1 := by
    simpa only [map_mul, map_one] using congrArg p
      (IsLocalization.Away.mul_invSelf (S := additiveLocalization K) (additiveGenerator K))
  have he : p (IsLocalization.Away.invSelf (additiveGenerator K)) =
      (p (algebraMap _ _ (additiveGenerator K)))⁻¹ := by
    have hn : p (algebraMap _ _ (additiveGenerator K)) ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hm
      exact zero_ne_one hm
    apply (mul_left_cancel₀ hn)
    exact hm.trans (mul_inv_cancel₀ hn).symm
  rw [parameter_localized, parameter_localized, hp, map_affine_eval,
    inverseLocalization_generator]
  exact he


end GroupActions
