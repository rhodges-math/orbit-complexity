import OrbitComplexity.SchubertGeometry.Deodhar.ChartImages

/-! # Relative chart images with a prescribed projection -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups SchubertGeometry
open GroupActions GroupActions.Variety CartesianMonoidalCategory MonoidalCategory

namespace SchubertGeometry

noncomputable section

universe u

private theorem chart_range_projection {K : Type u} [Field K]
    {X Y Z P D : Variety K} {A : Over (Spec (CommRingCat.of K))}
    (f : X.toOver ⟶ Z.toOver) (p : Y.toOver ⟶ Z.toOver)
    (r : P.toOver ≅ A) (e : A ≅ pullback f p) (j : Y.toOver ≅ D.toOver)
    (q : D.toOver ⟶ Z.toOver) (hq : j.hom ≫ q = p) :
    Set.range (mapPoints (X := P) (Y := D)
      (r.hom ≫ e.hom ≫ pullback.snd f p ≫ j.hom)) =
      (mapPoints (X := D) (Y := Z) q) ⁻¹'
        Set.range (mapPoints (X := X) (Y := Z) f) := by
  have hpb : IsPullback (pullback.fst f p) (pullback.snd f p ≫ j.hom) f q :=
    (IsPullback.of_hasPullback f p).of_iso (.refl _) (.refl _) j (.refl _)
      (by simp) (by simp) (by simp) (by simpa only [Iso.refl_hom, Category.comp_id] using hq.symm)
  have hroot := pullback_points_range f q (r ≪≫ e ≪≫ hpb.isoPullback)
  simpa only [Iso.trans_hom, Category.assoc, hpb.isoPullback_hom_snd] using hroot

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))
  (X D : Variety K) (f : X.toOver ⟶ (schubertCell G w).toOver)
  (g : X.toOver ⟶ (reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫ schubertCellInclusion G w)
  (j : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver ≅ D.toOver)
  (q : D.toOver ⟶ (schubertCell G w).toOver)

/-- A relative chart image is detected by its prescribed target projection. -/
theorem rankOneLiftMap_range_projection
    (hq : j.hom ≫ q = rankOneCellProjection G w i hi) (P : Variety K)
    (r : P.toOver ≅ X.toOver ⊗ (additiveVariety K).toOver) :
    Set.range (mapPoints (X := P) (Y := D)
      (r.hom ≫ (rankOneLiftIso G w i hi X f g hg).hom ≫
        pullback.snd f (rankOneCellProjection G w i hi) ≫ j.hom)) =
      (mapPoints (X := D) (Y := schubertCell G w) q) ⁻¹'
        Set.range (mapPoints (X := X) (Y := schubertCell G w) f) := by
  exact chart_range_projection f (rankOneCellProjection G w i hi) r
    (rankOneLiftIso G w i hi X f g hg) j q hq

end

end SchubertGeometry
