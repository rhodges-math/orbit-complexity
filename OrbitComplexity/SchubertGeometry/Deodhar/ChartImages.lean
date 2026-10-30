import OrbitComplexity.SchubertGeometry.Deodhar.ChartTransport
import OrbitComplexity.GroupActions.Varieties.PullbackImages

/-! # Images of relative cell maps

Relative cell maps transported through a cell isomorphism are preimmersions when the base
map is a preimmersion. Their rational images are the inverse images of the base images.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open GroupActions GroupActions.Variety CartesianMonoidalCategory MonoidalCategory
namespace SchubertGeometry
noncomputable section
universe u

private theorem post_iso_range {K : Type u} [Field K] {A B D : Variety K}
    (f : A.toOver ⟶ B.toOver) (j : B.toOver ≅ D.toOver) :
    Set.range (mapPoints (f ≫ j.hom)) =
      (mapPoints j.inv) ⁻¹' Set.range (mapPoints f) := by
  have he : ∀ a : A.points, mapPoints j.inv (mapPoints (f ≫ j.hom) a) = mapPoints f a := by
    intro a
    rw [← mapPoints_comp, Category.assoc, j.hom_inv_id, Category.comp_id]
  ext d
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (he a).symm⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply (pointsHomeomorph j).symm.injective
    exact (he a).trans ha

private theorem chart_range {K : Type u} [Field K] {X Y Z P D : Variety K}
    {A : Over (Spec (CommRingCat.of K))}
    (f : X.toOver ⟶ Z.toOver) (p : Y.toOver ⟶ Z.toOver)
    (r : P.toOver ≅ A) (e : A ≅ pullback f p) (j : Y.toOver ≅ D.toOver) :
    Set.range (mapPoints (r.hom ≫ e.hom ≫ pullback.snd f p ≫ j.hom)) =
      (mapPoints (j.inv ≫ p)) ⁻¹' Set.range (mapPoints f) := by
  have hroot := pullback_points_range f p (r ≪≫ e)
  simp only [Iso.trans_hom, Category.assoc] at hroot
  rw [← Category.assoc, ← Category.assoc, post_iso_range]
  simp only [Category.assoc]
  rw [hroot]
  ext d
  simp only [Set.mem_preimage, mapPoints_comp]

private theorem chart_preimmersion {K : Type u} [Field K] {X Y Z D : Variety K}
    {A : Over (Spec (CommRingCat.of K))}
    (f : X.toOver ⟶ Z.toOver) (p : Y.toOver ⟶ Z.toOver)
    (e : A ≅ pullback f p) (j : Y.toOver ≅ D.toOver) [IsPreimmersion f.left] :
    IsPreimmersion (e.hom ≫ pullback.snd f p ≫ j.hom).left := by
  have hpb : IsPullback (pullback.fst f p).left (pullback.snd f p).left f.left p.left :=
    (Over.forget (Spec (CommRingCat.of K))).map_isPullback (IsPullback.of_hasPullback f p)
  have : IsPreimmersion (pullback.snd f p).left :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hpb inferInstance
  have : IsIso e.hom.left := by
    change IsIso ((Over.forget (Spec (CommRingCat.of K))).map e.hom)
    infer_instance
  have : IsIso j.hom.left := by
    change IsIso ((Over.forget (Spec (CommRingCat.of K))).map j.hom)
    infer_instance
  change IsPreimmersion (e.hom.left ≫ (pullback.snd f p).left ≫ j.hom.left)
  infer_instance

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)
  (hi : G.rootBase.IsPos (G.rootSystem.weylGroupToPerm w i))
  (X D : Variety K) (f : X.toOver ⟶ (schubertCell G w).toOver)
  (g : X.toOver ⟶ (reductiveVariety G).toOver)
  (hg : g ≫ flagQuotientMorphism G = f ≫ schubertCellInclusion G w)
  (j : (schubertCell G (w * RootPairing.weylGroup.ofIdx G.rootSystem i)).toOver ≅ D.toOver)

/-- A transported relative chart over a preimmersion is a preimmersion. -/
theorem rankOneLiftMap_isPreimmersion [IsPreimmersion f.left] :
    IsPreimmersion ((rankOneLiftIso G w i hi X f g hg).hom ≫
      pullback.snd f (rankOneCellProjection G w i hi) ≫ j.hom).left :=
  chart_preimmersion f (rankOneCellProjection G w i hi)
    (rankOneLiftIso G w i hi X f g hg) j

/-- A relative chart has exactly the points projecting into its prescribed base image. -/
theorem rankOneLiftMap_points_range (P : Variety K)
    (r : P.toOver ≅ X.toOver ⊗ (additiveVariety K).toOver) :
    Set.range (mapPoints (r.hom ≫ (rankOneLiftIso G w i hi X f g hg).hom ≫
      pullback.snd f (rankOneCellProjection G w i hi) ≫ j.hom)) =
      (mapPoints (j.inv ≫ rankOneCellProjection G w i hi)) ⁻¹' Set.range (mapPoints f) :=
  chart_range f (rankOneCellProjection G w i hi) r
    (rankOneLiftIso G w i hi X f g hg) j

end
end SchubertGeometry
