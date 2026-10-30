import OrbitComplexity.SchubertGeometry.Parabolics.SimpleCurve
import OrbitComplexity.SchubertGeometry.Parabolics.SimpleFibre
import OrbitComplexity.GroupActions.Actions.Translations

/-! # Translated fibres of simple parabolic projection

Weyl translation identifies a simple Schubert curve with a fibre square of the
simple parabolic projection.
-/

noncomputable section
namespace SchubertGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups GroupActions
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj
universe u v

private theorem fibre_toSpec {C : Type u} [Category.{v} C] {A X Y S : C}
    (p : X ⟶ Y) (b : S ⟶ Y) [HasPullback p b]
    (tx : X ⟶ S) (ty : Y ⟶ S) (f : A ⟶ X) (ta : A ⟶ S)
    (hp : p ≫ ty = tx) (hb : b ≫ ty = 𝟙 S) (hf : f ≫ tx = ta)
    (e : A ≅ pullback p b) (he : e.hom ≫ pullback.fst p b = f) :
    e.hom ≫ pullback.snd p b = ta := by
  calc
    e.hom ≫ pullback.snd p b =
        (e.hom ≫ pullback.snd p b) ≫ (b ≫ ty) := by rw [hb, Category.comp_id]
    _ = e.hom ≫ ((pullback.snd p b ≫ b) ≫ ty) := by simp only [Category.assoc]
    _ = e.hom ≫ ((pullback.fst p b ≫ p) ≫ ty) := by rw [pullback.condition]
    _ = (e.hom ≫ pullback.fst p b) ≫ (p ≫ ty) := by simp only [Category.assoc]
    _ = f ≫ tx := by rw [he, hp]
    _ = ta := hf

private theorem translate_natural {K : Type u} [Field K] (H X Y : Variety K)
    [GrpObj H.toOver] [ModObj H.toOver X.toOver] [ModObj H.toOver Y.toOver]
    (f : X.toOver ⟶ Y.toOver) [IsModHom H.toOver f] (h : H.points) :
    Variety.translateMorphism H X h ≫ f = f ≫ Variety.translateMorphism H Y h := by
  simp only [Variety.translateMorphism, IsModHom.map_smul, ModObj.comp_smul,
    Category.comp_id, Category.id_comp, comp_toUnit_assoc]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) (w : G.weylGroup) (i : G.rootBase.support)

private abbrev simpleFibre : Variety K :=
  schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)

private theorem base_translation : (baseFlagPoint G).val ≫
    (Variety.translateMorphism (reductiveVariety G) (flagVariety G)
      (reductivePointsMulEquiv G (G.weylPoint w))).left = (weylFlagPoint G w).val := by
  have hflag : reductivePointsMulEquiv G (G.weylPoint w) • baseFlagPoint G =
      weylFlagPoint G w := by
    change reductivePointsMulEquiv G (G.weylPoint w) •
      flagVarietyPointsEquiv G (flagProjection G 1) = _
    rw [flagVarietyAction_points]
    change flagVarietyPointsEquiv G (flagProjection G (G.weylPoint w * 1)) = _
    rw [mul_one]
    rfl
  exact congrArg Subtype.val ((Variety.mapPoints_translateMorphism (reductiveVariety G)
    (flagVariety G) (reductivePointsMulEquiv G (G.weylPoint w))
      (baseFlagPoint G)).trans hflag)

/-- A translated simple Schubert curve is the fibre square of simple parabolic projection. -/
theorem simpleSchubertCurve_isPullback :
    IsPullback (simpleSchubertCurve G w i).left (simpleFibre G i).toSpec
      (partialFlagMorphism G {i}).left
      ((weylFlagPoint G w).val ≫ (partialFlagMorphism G {i}).left) := by
  let π : (flagVariety G).scheme ⟶ (partialFlagVariety G {i}).scheme :=
    (partialFlagMorphism G {i}).left
  let b : Spec (CommRingCat.of K) ⟶ (partialFlagVariety G {i}).scheme :=
    (baseFlagPoint G).val ≫ π
  let j : (simpleFibre G i).scheme ⟶ (flagVariety G).scheme :=
    (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).left
  obtain ⟨e, he⟩ := simpleSchubert_fibre G i
  have hp : π ≫ (partialFlagVariety G {i}).toSpec = (flagVariety G).toSpec :=
    (partialFlagMorphism G {i}).w
  have hb : b ≫ (partialFlagVariety G {i}).toSpec = 𝟙 _ := by
    change ((baseFlagPoint G).val ≫ π) ≫ _ = _
    rw [Category.assoc, hp, (baseFlagPoint G).property]
  have hs : e.hom ≫ pullback.snd π b = (simpleFibre G i).toSpec :=
    fibre_toSpec π b _ _ j _ hp hb
      (schubertInclusion G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).w e he
  have hbase : IsPullback j (simpleFibre G i).toSpec π b :=
    (IsPullback.of_hasPullback π b).of_iso' e (.refl _) (.refl _) (.refl _)
      (by simpa only [Iso.refl_hom, Category.comp_id] using he)
      (by simpa only [Iso.refl_hom, Category.comp_id] using hs) (by simp) (by simp)
  let g := reductivePointsMulEquiv G (G.weylPoint w)
  let a : (flagVariety G).scheme ≅ (flagVariety G).scheme :=
    (Over.forget (Spec (CommRingCat.of K))).mapIso
    (Variety.translationIso (reductiveVariety G) (flagVariety G) g)
  let d : (partialFlagVariety G {i}).scheme ≅ (partialFlagVariety G {i}).scheme :=
    (Over.forget (Spec (CommRingCat.of K))).mapIso
    (Variety.translationIso (reductiveVariety G) (partialFlagVariety G {i}) g)
  let : IsModHom (reductiveVariety G).toOver (partialFlagMorphism G {i}) :=
    partialFlagMorphism_isModHom G {i}
  have hn : π ≫ d.hom = a.hom ≫ π :=
    congrArg Over.Hom.left
      (translate_natural (reductiveVariety G) (flagVariety G)
        (partialFlagVariety G {i}) (partialFlagMorphism G {i}) g).symm
  have hcurve : IsPullback (j ≫ a.hom) (simpleFibre G i).toSpec π (b ≫ d.hom) :=
    hbase.of_iso (.refl _) a (.refl _) d (by simp) (by simp) hn (by simp)
  have hpoint : b ≫ d.hom = (weylFlagPoint G w).val ≫ π := by
    have ha : (baseFlagPoint G).val ≫ a.hom = (weylFlagPoint G w).val :=
      base_translation G w
    change ((baseFlagPoint G).val ≫ π) ≫ d.hom = _
    rw [Category.assoc, hn, ← Category.assoc, ha]
  rw [hpoint] at hcurve
  exact hcurve

end SchubertGeometry
