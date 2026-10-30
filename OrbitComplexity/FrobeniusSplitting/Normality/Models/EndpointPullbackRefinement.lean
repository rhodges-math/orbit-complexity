import OrbitComplexity.FrobeniusSplitting.Normality.Covers.PriorRefinedCover

/-! # The retained patches as inverse-image opens -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace FrobeniusSplitting

/-- The same patch identifies with the inverse-image open of the arithmetic
chart; both its arithmetic projection and its original endpoint refinement are retained. -/
theorem pullback_endpoint_refinement {Y X W P V : Scheme.{u}}
    (f : W ⟶ Y) [IsOpenImmersion f] (m : X ⟶ Y)
    (q : P ⟶ W) (j : P ⟶ X) (H : IsPullback q j f m)
    (a : P ⟶ V) (v : V ⟶ X) (ha : a ≫ v = j) :
    let U := m ⁻¹ᵁ f.opensRange
    ∃ e : P ≅ U.toScheme,
      e.hom ≫ U.ι = j ∧
      IsPullback (e.inv ≫ q) U.ι f m ∧
      (e.inv ≫ q) ≫ f = U.ι ≫ m ∧
      (e.inv ≫ a) ≫ v = U.ι := by
  let : IsOpenImmersion j := MorphismProperty.of_isPullback H inferInstance
  let U := m ⁻¹ᵁ f.opensRange
  have hj : Set.range j = Set.range (pullback.snd f m) := by
    rw [← H.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, Set.range_eq_univ.mpr H.isoPullback.hom.surjective, Set.image_univ]
  have hr : Set.range j = Set.range U.ι :=
    (hj.trans (IsOpenImmersion.range_pullbackSnd f m)).trans (Scheme.Opens.range_ι U).symm
  let e := IsOpenImmersion.isoOfRangeEq j U.ι hr
  have he : e.hom ≫ U.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac j U.ι hr
  have hi : e.inv ≫ j = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac j U.ι hr
  refine ⟨e, he, ?_, ?_, ?_⟩
  · exact H.of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simpa using hi) (by simp) (by simp)
  · rw [Category.assoc, H.w, ← Category.assoc, hi]
  · rw [Category.assoc, ha, hi]

end FrobeniusSplitting
