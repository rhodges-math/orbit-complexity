import OrbitComplexity.GroupActions.Rosenlicht.InvariantDomains

/-!
# Translation of invariant rational maps

Pullback on function fields describes the generic restriction of a translated
partial map. Invariant functions therefore give the same rational map after
translation, and its maximal domain is stable under translations.
-/

open CategoryTheory AlgebraicGeometry Topology

namespace GroupActions

noncomputable section

universe u

private lemma spec_stalkCongr {X : Scheme.{u}} (x y : X) (h : x = y) :
    Spec.map (X.presheaf.stalkCongr (.of_eq h)).hom ≫ X.fromSpecStalk x =
      X.fromSpecStalk y := by
  subst y
  change Spec.map (X.presheaf.stalkSpecializes (specializes_refl x)) ≫
    X.fromSpecStalk x = X.fromSpecStalk x
  rw [TopCat.Presheaf.stalkSpecializes_refl, Spec.map_id, Category.id_comp]

private lemma functionFieldMap_fromSpec {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ X) [IsDominant f] :
    Spec.map (CommRingCat.ofHom (functionFieldMap f)) ≫
        X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) ≫ f := by
  change Spec.map ((X.presheaf.stalkCongr (.of_eq (map_genericPoint f).symm)).hom ≫
    f.stalkMap (genericPoint X)) ≫ X.fromSpecStalk (genericPoint X) = _
  rw [Spec.map_comp, Category.assoc, spec_stalkCongr _ _ (map_genericPoint f).symm]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

private def precomposePartialMap {X Y : Scheme.{u}} (p : X.PartialMap Y) (e : X ≅ X) :
    X.PartialMap Y where
  domain := e.hom ⁻¹ᵁ p.domain
  dense_domain := p.dense_domain.preimage e.hom.homeomorph.isOpenMap
  hom := (e.hom ∣_ p.domain) ≫ p.hom

private lemma precomposePartialMap_field {X Y : Scheme.{u}} [IrreducibleSpace X]
    (p : X.PartialMap Y) (e : X ≅ X) :
    (precomposePartialMap p e).fromFunctionField =
      Spec.map (CommRingCat.ofHom (functionFieldMap e.hom)) ≫ p.fromFunctionField := by
  change (e.hom ⁻¹ᵁ p.domain).fromSpecStalkOfMem (genericPoint X) _ ≫
      (e.hom ∣_ p.domain) ≫ p.hom =
    Spec.map (CommRingCat.ofHom (functionFieldMap e.hom)) ≫
      p.domain.fromSpecStalkOfMem (genericPoint X) _ ≫ p.hom
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (fun g ↦ g ≫ p.hom)
  apply (cancel_mono p.domain.ι).mp
  simp only [Category.assoc, morphismRestrict_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι]
  erw [Scheme.Opens.fromSpecStalkOfMem_ι_assoc]
  exact (functionFieldMap_fromSpec e.hom).symm

namespace Variety

variable {K : Type u} [Field K] (H X : GroupActions.Variety K)
variable [GrpObj H.toOver] [ModObj H.toOver X.toOver] [IrreducibleSpace X.scheme]

private lemma invariantMap_generic_translate (h : H.points) :
    Spec.map (CommRingCat.ofHom
      (functionFieldMap (schemeTranslationHom H X h).inv)) ≫
        (invariantMap H X).fromFunctionField = (invariantMap H X).fromFunctionField := by
  let _ : X.scheme.Over (Spec (.of K)) := ⟨X.toSpec⟩
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  have := invariantField_essFiniteType H X
  let _ := functionFieldAction (schemeTranslationHom H X)
  let E := invariantField H X
  have hf : (invariantMap H X).fromFunctionField =
      Spec.map (CommRingCat.ofHom (E.val.comp (fieldModelAlgebra K E).val).toRingHom) :=
    intermediateRationalMap_field K E
  rw [hf]
  erw [← Spec.map_comp]
  congr 1
  ext a
  exact a.val.property h

private lemma invariantMap_precompose (h : H.points) :
    (precomposePartialMap (invariantMap H X).toPartialMap
      (schemeTranslationHom H X h).symm).toRationalMap = invariantMap H X := by
  have : IsIntegral X.scheme := isIntegral_of_irreducibleSpace_of_isReduced X.scheme
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap, precomposePartialMap_field]
  have hp : (invariantMap H X).toPartialMap.fromFunctionField =
      (invariantMap H X).fromFunctionField := by
    rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.toRationalMap_toPartialMap]
  rw [hp]
  exact invariantMap_generic_translate H X h

private lemma invariantMap_preimage_le (h : H.points) :
    (schemeTranslationHom H X h).inv ⁻¹ᵁ (invariantMap H X).domain ≤
      (invariantMap H X).domain := by
  have hl := (precomposePartialMap (invariantMap H X).toPartialMap
    (schemeTranslationHom H X h).symm).le_domain_toRationalMap
  rw [invariantMap_precompose H X h] at hl
  exact hl

/-- The maximal domain of the invariant rational map is stable under translation. -/
theorem invariantMap_domain_translate (h : H.points) :
    (translateMorphism H X h).left ⁻¹ᵁ (invariantMap H X).domain =
      (invariantMap H X).domain := by
  have hinv : (schemeTranslationHom H X h⁻¹).inv =
      (schemeTranslationHom H X h).hom := by
    rw [map_inv]
    rfl
  apply le_antisymm
  · simpa only [hinv, schemeTranslationHom_hom] using invariantMap_preimage_le H X h⁻¹
  · intro x hx
    apply invariantMap_preimage_le H X h
    change (schemeTranslationHom H X h).inv
      ((schemeTranslationHom H X h).hom x) ∈ (invariantMap H X).domain
    rw [← Scheme.Hom.comp_apply]
    erw [Iso.hom_inv_id]
    exact hx

private lemma invariantPartial_translate (h : H.points) :
    (precomposePartialMap (invariantMap H X).toPartialMap
      (schemeTranslationHom H X h).symm).hom =
      X.scheme.homOfLE (invariantMap_preimage_le H X h) ≫
        (invariantMap H X).toPartialMap.hom := by
  have he : (precomposePartialMap (invariantMap H X).toPartialMap
      (schemeTranslationHom H X h).symm).equiv (invariantMap H X).toPartialMap := by
    apply Scheme.PartialMap.toRationalMap_eq_iff.mp
    rw [invariantMap_precompose, Scheme.RationalMap.toRationalMap_toPartialMap]
  have he' := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme)
    (g := (invariantMap H X).toPartialMap)
    (precomposePartialMap (invariantMap H X).toPartialMap
      (schemeTranslationHom H X h).symm).dense_domain le_rfl
        (invariantMap_preimage_le H X h)).mp he
  change X.scheme.homOfLE le_rfl ≫
      (precomposePartialMap (invariantMap H X).toPartialMap
        (schemeTranslationHom H X h).symm).hom =
    X.scheme.homOfLE (invariantMap_preimage_le H X h) ≫
      (invariantMap H X).toPartialMap.hom at he'
  rw [Scheme.homOfLE_rfl, Category.id_comp] at he'
  exact he'

/-- The morphism defined by invariant functions is constant under every translation
at points in its domain. -/
theorem invariantMorphism_translate (h : H.points) (x : X.scheme)
    (hx : x ∈ (invariantMap H X).domain)
    (htx : (translateMorphism H X h).left x ∈ (invariantMap H X).domain) :
    (invariantMorphism H X).left ⟨(translateMorphism H X h).left x, htx⟩ =
      (invariantMorphism H X).left ⟨x, hx⟩ := by
  let p := precomposePartialMap (invariantMap H X).toPartialMap
    (schemeTranslationHom H X h⁻¹).symm
  have hi : (schemeTranslationHom H X h⁻¹).inv = (translateMorphism H X h).left := by
    rw [map_inv]
    rfl
  let a : p.domain := ⟨x, by
    change (schemeTranslationHom H X h⁻¹).inv x ∈ (invariantMap H X).domain
    rw [hi]
    exact htx⟩
  have he := congrArg (fun f : p.domain.toScheme ⟶ (invariantModel H X).scheme ↦ f a)
    (invariantPartial_translate H X h⁻¹)
  change (invariantMap H X).toPartialMap.hom
      (((schemeTranslationHom H X h⁻¹).inv ∣_ (invariantMap H X).domain) a) =
    (invariantMap H X).toPartialMap.hom
      (X.scheme.homOfLE (invariantMap_preimage_le H X h⁻¹) a) at he
  have hl : ((schemeTranslationHom H X h⁻¹).inv ∣_ (invariantMap H X).domain) a =
      ⟨(translateMorphism H X h).left x, htx⟩ := by
    apply Subtype.ext
    simpa only [hi, a] using morphismRestrict_base_coe
      (schemeTranslationHom H X h⁻¹).inv (invariantMap H X).domain a
  have hr : X.scheme.homOfLE (invariantMap_preimage_le H X h⁻¹) a = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ a
  rw [hl, hr] at he
  exact he

end Variety

end

end GroupActions
