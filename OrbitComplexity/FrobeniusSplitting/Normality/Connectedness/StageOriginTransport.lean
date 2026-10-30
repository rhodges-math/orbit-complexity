import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.StageSections
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.StageAnchorMaps

set_option autoImplicit false

/-! # Coefficient transitions of sections and anchors

Sections of a model commute with its coefficient transitions. The induced
anchor maps therefore extend to the anchors of the same sections at the
later coefficient stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobeniusSplitting

universe u

private theorem section_transition_of_pullback
    {C : Type*} [Category C] {B Bi Bj X Pi Pj : C}
    {κi : Bi ⟶ B} {κj : Bj ⟶ B} {ρ : Bj ⟶ Bi} {a : X ⟶ B}
    {pi : Pi ⟶ Bi} {qi : Pi ⟶ X} {pj : Pj ⟶ Bj} {qj : Pj ⟶ X}
    (hcart : IsPullback pi qi κi a)
    (t : Pj ⟶ Pi) (si : Bi ⟶ Pi) (sj : Bj ⟶ Pj) (s : B ⟶ X)
    (hκ : ρ ≫ κi = κj)
    (htbase : t ≫ pi = pj ≫ ρ) (htoriginal : t ≫ qi = qj)
    (hsibase : si ≫ pi = 𝟙 Bi) (hsioriginal : si ≫ qi = κi ≫ s)
    (hsjbase : sj ≫ pj = 𝟙 Bj) (hsjoriginal : sj ≫ qj = κj ≫ s) :
    sj ≫ t = ρ ≫ si := by
  apply hcart.hom_ext
  · calc
      (sj ≫ t) ≫ pi = sj ≫ (t ≫ pi) := Category.assoc _ _ _
      _ = sj ≫ (pj ≫ ρ) := congrArg (fun k => sj ≫ k) htbase
      _ = (sj ≫ pj) ≫ ρ := (Category.assoc _ _ _).symm
      _ = ρ := by rw [hsjbase, Category.id_comp]
      _ = ρ ≫ (si ≫ pi) := by rw [hsibase, Category.comp_id]
      _ = (ρ ≫ si) ≫ pi := (Category.assoc _ _ _).symm
  · calc
      (sj ≫ t) ≫ qi = sj ≫ (t ≫ qi) := Category.assoc _ _ _
      _ = sj ≫ qj := congrArg (fun k => sj ≫ k) htoriginal
      _ = κj ≫ s := hsjoriginal
      _ = (ρ ≫ κi) ≫ s := congrArg (fun k => k ≫ s) hκ.symm
      _ = ρ ≫ (κi ≫ s) := Category.assoc _ _ _
      _ = ρ ≫ (si ≫ qi) := congrArg (fun k => ρ ≫ k) hsioriginal.symm
      _ = (ρ ≫ si) ≫ qi := (Category.assoc _ _ _).symm

private theorem anchorArrow_eq_of_pullback
    {C : Type*} [Category C] {B B' : C}
    {U X Y : Over B} {U' X' Y' : Over B'}
    {κ : B' ⟶ B} {pY : Y'.left ⟶ Y.left}
    (hY : IsPullback pY Y'.hom Y.hom κ)
    (pU : U'.left ⟶ U.left) (pX : X'.left ⟶ X.left)
    (hU : pU ≫ U.hom = U'.hom ≫ κ)
    (s : B ⟶ X.left) (hs : s ≫ X.hom = 𝟙 B)
    (s' : B' ⟶ X'.left) (hs' : s' ≫ X'.hom = 𝟙 B')
    (hsection : s' ≫ pX = κ ≫ s)
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (hf : f'.left ≫ pY = pX ≫ f.left)
    (g : U' ⟶ Y')
    (hg : g.left ≫ pY = pU ≫ (anchorArrow U s hs f).left) :
    g = anchorArrow U' s' hs' f' := by
  have ha : (anchorArrow U' s' hs' f').left ≫ pY =
      pU ≫ (anchorArrow U s hs f).left := by
    change ((U'.hom ≫ s') ≫ f'.left) ≫ pY = pU ≫ ((U.hom ≫ s) ≫ f.left)
    simp only [Category.assoc]
    rw [hf, ← Category.assoc s' pX f.left, hsection]
    simp only [Category.assoc]
    rw [← Category.assoc U'.hom κ (s ≫ f.left), ← hU]
    simp only [Category.assoc]
  apply Over.OverMorphism.ext
  exact hY.hom_ext (hg.trans ha.symm) (g.w.trans (anchorArrow U' s' hs' f').w.symm)

private theorem stageCoefficient_triangle {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {i j : CoefficientStage S} (hij : i ≤ j) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom) := by
  have hring : (Subalgebra.inclusion hij).toRingHom.comp
        (Subalgebra.inclusion i.property.2).toRingHom =
      (Subalgebra.inclusion j.property.2).toRingHom := by
    ext x
    rfl
  have hcat :
      CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom ≫
          CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom =
        CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom := by
    change CommRingCat.ofHom ((Subalgebra.inclusion hij).toRingHom.comp
      (Subalgebra.inclusion i.property.2).toRingHom) = _
    exact congrArg CommRingCat.ofHom hring
  rw [← Spec.map_comp]
  exact congrArg
    (fun f : CommRingCat.of S ⟶ CommRingCat.of j.val => Spec.map f) hcat

/-- The origin of a section at a later coefficient stage commutes with the
transition on the same model. -/
theorem stageOriginSection_transition {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X : Scheme.{u}} (a : X ⟶ Spec (.of S))
    (s : Spec (.of S) ⟶ X) (hs : s ≫ a = 𝟙 _)
    {i j : CoefficientStage S} (hij : i ≤ j) :
    stageOriginSection S a s hs j ≫ stageScalarTransition S a hij =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom) ≫
        stageOriginSection S a s hs i := by
  let κi := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion i.property.2).toRingHom)
  let κj := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hij).toRingHom)
  have hsi : stageOriginSection S a s hs i ≫ pullback.snd κi a = κi ≫ s :=
    pullbackSection_original κi a s hs
  have hsj : stageOriginSection S a s hs j ≫ pullback.snd κj a = κj ≫ s :=
    pullbackSection_original κj a s hs
  exact section_transition_of_pullback (IsPullback.of_hasPullback κi a)
    (stageScalarTransition S a hij)
    (stageOriginSection S a s hs i) (stageOriginSection S a s hs j) s
    (show ρ ≫ κi = κj from stageCoefficient_triangle S hij)
    (stageScalarTransition_fst S a hij) (stageScalarTransition_snd S a hij)
    (stageOriginSection_base S a s hs i) hsi
    (stageOriginSection_base S a s hs j) hsj

/-- Extending an anchor map on a model gives the anchor formed from the
origin and the extended map at the later coefficient stage. -/
theorem anchorArrow_extend {K : Type u} [CommRing K]
    (S : Subalgebra ℤ K) {X Y U : Scheme.{u}}
    (a : X ⟶ Spec (.of S)) (b : Y ⟶ Spec (.of S)) (c : U ⟶ Spec (.of S))
    (s : Spec (.of S) ⟶ X) (hs : s ≫ a = 𝟙 _)
    {i j : CoefficientStage S} (hij : i ≤ j)
    (f : stageScalarModel S a i ⟶ stageScalarModel S b i) :
    extendModelMorphism S c b hij
        (anchorArrow (stageScalarModel S c i)
          (stageOriginSection S a s hs i) (stageOriginSection_base S a s hs i) f) =
      anchorArrow (stageScalarModel S c j)
        (stageOriginSection S a s hs j) (stageOriginSection_base S a s hs j)
        (extendModelMorphism S a b hij f) := by
  exact anchorArrow_eq_of_pullback
    (U := stageScalarModel S c i) (X := stageScalarModel S a i)
    (Y := stageScalarModel S b i)
    (U' := stageScalarModel S c j) (X' := stageScalarModel S a j)
    (Y' := stageScalarModel S b j)
    (stageScalarCartesian S b hij)
    (stageScalarTransition S c hij) (stageScalarTransition S a hij)
    (stageScalarTransition_fst S c hij)
    (stageOriginSection S a s hs i) (stageOriginSection_base S a s hs i)
    (stageOriginSection S a s hs j) (stageOriginSection_base S a s hs j)
    (stageOriginSection_transition S a s hs hij)
    f (extendModelMorphism S a b hij f)
    (extendModelMorphism_transition S a b hij f)
    (extendModelMorphism S c b hij
      (anchorArrow (stageScalarModel S c i)
        (stageOriginSection S a s hs i) (stageOriginSection_base S a s hs i) f))
    (extendModelMorphism_transition S c b hij
      (anchorArrow (stageScalarModel S c i)
        (stageOriginSection S a s hs i) (stageOriginSection_base S a s hs i) f))

end FrobeniusSplitting
