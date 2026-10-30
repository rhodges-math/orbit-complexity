import OrbitComplexity.GroupActions.Varieties.CoordinateInversion
import OrbitComplexity.GroupActions.Varieties.AdditiveOpens

/-! # Rational images in additive product charts -/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory

namespace GroupActions.Variety

noncomputable section

universe u

variable {K : Type u} [Field K]

private theorem points_comp {X Y : GroupActions.Variety K}
    (f : X.toOver ⟶ Y.toOver) (x : X.points) :
    Y.pointsEquivOverHom (mapPoints f x) = X.pointsEquivOverHom x ≫ f := rfl

private theorem tensorFactor_points_range (X Y Z P Q : GroupActions.Variety K)
    (r : P.toOver ≅ X.toOver ⊗ Z.toOver) (e : Q.toOver ≅ X.toOver ⊗ Y.toOver)
    (f : Y.toOver ⟶ Z.toOver) :
    Set.range (mapPoints (e.hom ≫ (𝟙 X.toOver ⊗ₘ f) ≫ r.inv)) =
      {p | mapPoints (r.hom ≫ snd X.toOver Z.toOver) p ∈ Set.range (mapPoints f)} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨mapPoints (e.hom ≫ snd X.toOver Y.toOver) q, ?_⟩
    apply Z.pointsEquivOverHom.injective
    simp only [points_comp, Category.assoc, Iso.inv_hom_id_assoc,
      tensorHom_snd]
  · rintro ⟨y, hy⟩
    let x := X.pointsEquivOverHom.symm
      (P.pointsEquivOverHom p ≫ r.hom ≫ fst X.toOver Z.toOver)
    let q := Q.pointsEquivOverHom.symm
      (lift (X.pointsEquivOverHom x) (Y.pointsEquivOverHom y) ≫ e.inv)
    refine ⟨q, ?_⟩
    apply P.pointsEquivOverHom.injective
    rw [points_comp]
    dsimp only [q]
    rw [Equiv.apply_symm_apply]
    apply (cancel_mono r.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst]
      dsimp only [x]
      rw [Equiv.apply_symm_apply]
    · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc]
      exact congrArg Z.pointsEquivOverHom hy

/-- A zero section in an additive product chart has exactly the zero-coordinate points. -/
theorem zeroSection_points_range (X F : GroupActions.Variety K)
    (r : F.toOver ≅ X.toOver ⊗ (additiveVariety K).toOver) :
    Set.range (mapPoints (lift (𝟙 X.toOver)
      (toUnit X.toOver ≫
        (additiveVariety K).pointsEquivOverHom (additivePointsEquiv K 0)) ≫ r.inv)) =
      {p | mapPoints (r.hom ≫ snd X.toOver (additiveVariety K).toOver) p =
        additivePointsEquiv K 0} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    apply (additiveVariety K).pointsEquivOverHom.injective
    simp only [points_comp, Category.assoc, Iso.inv_hom_id_assoc, lift_snd]
    have hu : X.pointsEquivOverHom x ≫ toUnit X.toOver =
        𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := toUnit_unique _ _
    rw [← Category.assoc, hu, Category.id_comp]
  · intro hp
    let x := mapPoints (r.hom ≫ fst X.toOver (additiveVariety K).toOver) p
    refine ⟨x, ?_⟩
    apply F.pointsEquivOverHom.injective
    rw [points_comp]
    apply (cancel_mono r.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, x, points_comp, Category.comp_id]
    · simp only [Category.assoc, lift_snd]
      have hu : X.pointsEquivOverHom x ≫ toUnit X.toOver =
          𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := toUnit_unique _ _
      rw [← Category.assoc, hu, Category.id_comp]
      exact congrArg (additiveVariety K).pointsEquivOverHom hp.symm

/-- A reciprocal punctured factor has exactly the nonzero-coordinate points. -/
theorem reciprocalFactor_points_range [IsAlgClosed K] (X F Q : GroupActions.Variety K)
    (r : F.toOver ≅ X.toOver ⊗ (additiveVariety K).toOver)
    (e : Q.toOver ≅ X.toOver ⊗
      ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver) :
    Set.range (mapPoints (e.hom ≫
      (𝟙 X.toOver ⊗ₘ ((puncturedAdditiveInvIso K).hom ≫
        (additiveVariety K).openInclusion (additiveNonzero K))) ≫ r.inv)) =
      {p | (additivePointsEquiv K).symm
        (mapPoints (r.hom ≫ snd X.toOver (additiveVariety K).toOver) p) ≠ 0} := by
  rw [tensorFactor_points_range]
  have hr : Set.range (mapPoints ((puncturedAdditiveInvIso K).hom ≫
      (additiveVariety K).openInclusion (additiveNonzero K))) =
      Set.range (mapPoints ((additiveVariety K).openInclusion (additiveNonzero K))) := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨mapPoints (puncturedAdditiveInvIso K).hom b,
        (mapPoints_comp _ _ _).symm⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨c, hc⟩ := (pointsHomeomorph (puncturedAdditiveInvIso K)).surjective b
      exact ⟨c, (mapPoints_comp _ _ _).trans
        (congrArg (mapPoints ((additiveVariety K).openInclusion (additiveNonzero K))) hc)⟩
  rw [hr, additiveNonzero_points]
  rfl

end

end GroupActions.Variety
