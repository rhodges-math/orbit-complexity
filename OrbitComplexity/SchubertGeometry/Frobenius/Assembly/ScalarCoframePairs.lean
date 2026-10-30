import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingFieldOverlaps
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareComposition
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareRestriction
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameReflection
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Equality of scalar coframes on chart overlaps

The scalar overlap and its injective coordinate comparison are constructed
from the individual chart squares. Individual comparisons with one field
coframe then reflect equality of the two coframes on the scheme pullback.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting.CharacterLine

open private pulled_coframe from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareComposition

namespace SchubertGeometry

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def coframeComposite {A B Y : Scheme.{u}} (v : A ⟶ B) (b : B ⟶ Y)
    (L : Y.Modules) (E : (Scheme.Modules.pullback b).obj L ≅ unitModule B) :
    (Scheme.Modules.pullback (v ≫ b)).obj L ≅ unitModule A :=
  ((pullbackComp v b).app L).symm ≪≫ (Scheme.Modules.pullback v).mapIso E ≪≫
    pullbackObjUnitIso v

private theorem square_k_eq {A B Y Z : Scheme.{u}} (q : Z ⟶ Y) (a : A ⟶ Z)
    (b : B ⟶ Y) (k₀ k₁ : A ⟶ B) (hk : k₀ = k₁)
    (h₀ : k₀ ≫ b = a ≫ q) (h₁ : k₁ ≫ b = a ≫ q) (L : Y.Modules)
    (E : (Scheme.Modules.pullback b).obj L ≅ unitModule B) :
    squareFrameIso q a b k₀ h₀ L E = squareFrameIso q a b k₁ h₁ L E := by
  subst k₁
  rfl

private theorem square_b_eq {A B Y Z : Scheme.{u}} (q : Z ⟶ Y) (a : A ⟶ Z)
    (b₀ b₁ : B ⟶ Y) (hb : b₀ = b₁) (k : A ⟶ B)
    (h₀ : k ≫ b₀ = a ≫ q) (h₁ : k ≫ b₁ = a ≫ q) (L : Y.Modules)
    (E : (Scheme.Modules.pullback b₁).obj L ≅ unitModule B) :
    squareFrameIso q a b₀ k h₀ L ((pullbackCongr hb).app L ≪≫ E) =
      squareFrameIso q a b₁ k h₁ L E := by
  subst b₁
  change squareFrameIso q a b₀ k h₀ L (Iso.refl _ ≪≫ E) =
    squareFrameIso q a b₀ k h₁ L E
  exact congrArg (fun F => squareFrameIso q a b₀ k h₀ L F) (Iso.refl_trans E)

private theorem square_a_eq {A B Y Z : Scheme.{u}} (q : Z ⟶ Y)
    (a₀ a₁ : A ⟶ Z) (ha : a₀ = a₁) (b : B ⟶ Y) (k : A ⟶ B)
    (h₀ : k ≫ b = a₀ ≫ q) (h₁ : k ≫ b = a₁ ≫ q) (L : Y.Modules)
    (E : (Scheme.Modules.pullback b).obj L ≅ unitModule B) :
    squareFrameIso q a₀ b k h₀ L E =
      (pullbackCongr ha).app ((Scheme.Modules.pullback q).obj L) ≪≫
        squareFrameIso q a₁ b k h₁ L E := by
  subst a₁
  change squareFrameIso q a₀ b k h₀ L E =
    Iso.refl _ ≪≫ squareFrameIso q a₀ b k h₁ L E
  exact (Iso.refl_trans (squareFrameIso q a₀ b k h₀ L E)).symm

private theorem frame_a_eq {A Z : Scheme.{u}} (a₀ a₁ : A ⟶ Z)
    (ha : a₀ = a₁) (M : Z.Modules) (F : M ≅ unitModule Z) :
    (pullbackCongr ha).app M ≪≫ (Scheme.Modules.pullback a₁).mapIso F ≪≫
      pullbackObjUnitIso a₁ =
        (Scheme.Modules.pullback a₀).mapIso F ≪≫ pullbackObjUnitIso a₀ := by
  subst a₁
  change Iso.refl _ ≪≫ (Scheme.Modules.pullback a₀).mapIso F ≪≫
    pullbackObjUnitIso a₀ = _
  simp only [Iso.refl_trans]

private theorem refined_frame {A B C D Y Z : Scheme.{u}}
    (q : Z ⟶ Y) (L : Y.Modules)
    (FK : (Scheme.Modules.pullback q).obj L ≅ unitModule Z)
    (a : A ⟶ Z) (b : B ⟶ Y) (k : A ⟶ B) (h : k ≫ b = a ≫ q)
    (E : (Scheme.Modules.pullback b).obj L ≅ unitModule B)
    (he : squareFrameIso q a b k h L E =
      (Scheme.Modules.pullback a).mapIso FK ≪≫ pullbackObjUnitIso a)
    (c : C ⟶ A) (v : D ⟶ B) (w : C ⟶ D) (hw : w ≫ v = c ≫ k)
    (htotal : w ≫ (v ≫ b) = (c ≫ a) ≫ q) :
    squareFrameIso q (c ≫ a) (v ≫ b) w htotal L (coframeComposite v b L E) =
      (Scheme.Modules.pullback (c ≫ a)).mapIso FK ≪≫ pullbackObjUnitIso (c ≫ a) := by
  have h₁ : (w ≫ v) ≫ b = (c ≫ a) ≫ q :=
    (Category.assoc w v b).trans htotal
  have h₂ : (c ≫ k) ≫ b = (c ≫ a) ≫ q := by
    rw [← hw]
    exact h₁
  calc
    _ = squareFrameIso q (c ≫ a) b (w ≫ v) h₁ L E :=
      squareFrameIso_chart_comp q (c ≫ a) b w v htotal h₁ L E
    _ = squareFrameIso q (c ≫ a) b (c ≫ k) h₂ L E :=
      square_k_eq q (c ≫ a) b (w ≫ v) (c ≫ k) hw h₁ h₂ L E
    _ = coframeComposite c a ((Scheme.Modules.pullback q).obj L)
        (squareFrameIso q a b k h L E) :=
      squareFrameIso_domain_comp q a b k h c h₂ L E
    _ = coframeComposite c a ((Scheme.Modules.pullback q).obj L)
        ((Scheme.Modules.pullback a).mapIso FK ≪≫ pullbackObjUnitIso a) := by rw [he]
    _ = _ := by
      apply Iso.ext
      exact pulled_coframe c a ((Scheme.Modules.pullback q).obj L) FK

private theorem square_reflect {A B Y Z : Scheme.{u}} (q : Z ⟶ Y) (a : A ⟶ Z)
    (b : B ⟶ Y) (k : A ⟶ B) (h : k ≫ b = a ≫ q) (L : Y.Modules)
    (E F : (Scheme.Modules.pullback b).obj L ≅ unitModule B)
    (hinj : Function.Injective k.appTop.hom)
    (heq : squareFrameIso q a b k h L E = squareFrameIso q a b k h L F) : E = F := by
  let H := (pullbackComp a q).app L ≪≫ (pullbackCongr h.symm).app L ≪≫
    ((pullbackComp k b).app L).symm
  have hh : H.hom ≫ ((Scheme.Modules.pullback k).mapIso E ≪≫ pullbackObjUnitIso k).hom =
      H.hom ≫ ((Scheme.Modules.pullback k).mapIso F ≪≫ pullbackObjUnitIso k).hom :=
    congrArg Iso.hom heq
  apply FrobeniusSplitting.RetainedCharacter.frame_eq_of_pullback k
    ((Scheme.Modules.pullback b).obj L) E F hinj
  apply Iso.ext
  exact (cancel_epi H.hom).mp hh

/-- Individual chart comparisons with one field coframe imply equality of
both pulled-back arithmetic coframes on their scheme overlap. -/
theorem scalarCoframe_pair_eq {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (hR : Function.Injective (algebraMap R K))
    {Y Z A B AK BK : Scheme.{u}} [Y.IsSeparated] [IsAffine A] [IsAffine B]
    (base : Y ⟶ Spec (.of R)) [Smooth base]
    (f : A ⟶ Y) (g : B ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    (fK : AK ⟶ Z) (gK : BK ⟶ Z) (u : AK ⟶ A) (v : BK ⟶ B) (z : Z ⟶ Y)
    (hu : u ≫ f = fK ≫ z) (hv : v ≫ g = gK ≫ z)
    (tA : AK ⟶ Spec (.of K))
    (hA : IsPullback u tA (f ≫ base)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hB : IsPullback v gK g z) (L : Y.Modules)
    (FK : (Scheme.Modules.pullback z).obj L ≅ unitModule Z)
    (E : (Scheme.Modules.pullback f).obj L ≅ unitModule A)
    (F : (Scheme.Modules.pullback g).obj L ≅ unitModule B)
    (he : squareFrameIso z fK f u hu L E =
      (Scheme.Modules.pullback fK).mapIso FK ≪≫ pullbackObjUnitIso fK)
    (hf : squareFrameIso z gK g v hv L F =
      (Scheme.Modules.pullback gK).mapIso FK ≪≫ pullbackObjUnitIso gK) :
    coframeComposite (pullback.fst f g) f L E =
      (pullbackCongr (pullback.condition (f := f) (g := g))).app L ≪≫
        coframeComposite (pullback.snd f g) g L F := by
  let qP := pullback.map fK gK f g u v z hu.symm hv.symm
  have hcoords := matchingOverlap_field_coordinates hR base f g fK gK u v z hu hv tA hA hB
  have hinj : Function.Injective qP.appTop.hom := hcoords.2.2.2.1
  have hqfst : qP ≫ pullback.fst f g = pullback.fst fK gK ≫ u :=
    pullback.lift_fst _ _ _
  have hqsnd : qP ≫ pullback.snd f g = pullback.snd fK gK ≫ v :=
    pullback.lift_snd _ _ _
  have h₀ : qP ≫ (pullback.fst f g ≫ f) = (pullback.fst fK gK ≫ fK) ≫ z := by
    rw [← Category.assoc, hqfst, Category.assoc, hu, ← Category.assoc]
  have h₁ : qP ≫ (pullback.snd f g ≫ g) = (pullback.snd fK gK ≫ gK) ≫ z := by
    rw [← Category.assoc, hqsnd, Category.assoc, hv, ← Category.assoc]
  have h₂ : qP ≫ (pullback.snd f g ≫ g) = (pullback.fst fK gK ≫ fK) ≫ z := by
    rw [← pullback.condition (f := f) (g := g)]
    exact h₀
  have hleft := refined_frame z L FK fK f u hu E he
    (pullback.fst fK gK) (pullback.fst f g) qP
    hqfst h₀
  have hright := refined_frame z L FK gK g v hv F hf
    (pullback.snd fK gK) (pullback.snd f g) qP
    hqsnd h₁
  apply square_reflect z (pullback.fst fK gK ≫ fK) (pullback.fst f g ≫ f)
    qP h₀ L _ _ hinj
  refine hleft.trans ?_
  symm
  calc
    _ = squareFrameIso z (pullback.fst fK gK ≫ fK) (pullback.snd f g ≫ g) qP h₂ L
        (coframeComposite (pullback.snd f g) g L F) :=
      square_b_eq z (pullback.fst fK gK ≫ fK) (pullback.fst f g ≫ f)
        (pullback.snd f g ≫ g) (pullback.condition (f := f) (g := g))
        qP h₀ h₂ L (coframeComposite (pullback.snd f g) g L F)
    _ = (pullbackCongr (pullback.condition (f := fK) (g := gK))).app
          ((Scheme.Modules.pullback z).obj L) ≪≫
        squareFrameIso z (pullback.snd fK gK ≫ gK) (pullback.snd f g ≫ g) qP h₁ L
          (coframeComposite (pullback.snd f g) g L F) :=
      square_a_eq z (pullback.fst fK gK ≫ fK) (pullback.snd fK gK ≫ gK)
        (pullback.condition (f := fK) (g := gK)) (pullback.snd f g ≫ g)
        qP h₂ h₁ L (coframeComposite (pullback.snd f g) g L F)
    _ = (pullbackCongr (pullback.condition (f := fK) (g := gK))).app
          ((Scheme.Modules.pullback z).obj L) ≪≫
        ((Scheme.Modules.pullback (pullback.snd fK gK ≫ gK)).mapIso FK ≪≫
          pullbackObjUnitIso (pullback.snd fK gK ≫ gK)) := by rw [hright]
    _ = _ := frame_a_eq _ _ (pullback.condition (f := fK) (g := gK)) _ FK

end SchubertGeometry
