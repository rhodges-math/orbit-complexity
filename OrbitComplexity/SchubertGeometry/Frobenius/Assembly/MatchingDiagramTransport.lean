import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPullback
import Mathlib.CategoryTheory.Whiskering
import Batteries.Tactic.Lint

/-! # Matching lines under isomorphisms of coefficient diagrams

Precomposition of a gluing cocone keeps its point. The induced matching-line
isomorphism carries matching sections to matching sections at every power.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule

section Cocones

variable {T : Type u} [CommRing T] {I : Type v} [Category.{w} I]
    {N F : I ⥤ CommAlgCat.{u} T}

/-- The ring-map comparison associated with an algebra-diagram isomorphism. -/
def matchingIsoRingMap (e : N ≅ F) :
    N ⋙ forget₂ (CommAlgCat T) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat T) CommRingCat :=
  Functor.whiskerRight e.hom (forget₂ (CommAlgCat T) CommRingCat)

/-- Transport of the gluing diagram with its original cocone point. -/
def matchingIsoCocone (e : N ≅ F) (cN : Cocone (N.op ⋙ algSpec (.of T))) :
    Cocone (F.op ⋙ algSpec (.of T)) :=
  (Cocone.precompose (Functor.isoWhiskerRight (NatIso.op e) (algSpec (.of T))).hom).obj cN

/-- Transport along a diagram isomorphism preserves the colimit property. -/
def matchingIsoCoconeColimit (e : N ≅ F)
    (cN : Cocone (N.op ⋙ algSpec (.of T))) (hcN : IsColimit cN) :
    IsColimit (matchingIsoCocone e cN) :=
  (IsColimit.precomposeHomEquiv
    (Functor.isoWhiskerRight (NatIso.op e) (algSpec (.of T))) cN).symm hcN

/-- The transported legs commute with the identity on the original glued scheme. -/
theorem matchingIsoCocone_leg (e : N ≅ F)
    (cN : Cocone (N.op ⋙ algSpec (.of T))) (s : I) :
    Spec.map ((matchingIsoRingMap e).app s) ≫ (cN.ι.app (op s)).left =
      ((matchingIsoCocone e cN).ι.app (op s)).left ≫ 𝟙 cN.pt.left := by
  exact (Category.comp_id
    (Spec.map ((matchingIsoRingMap e).app s) ≫ (cN.ι.app (op s)).left)).symm

end Cocones

private theorem identity_section {X : Scheme.{u}} {L M : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback (𝟙 X)).obj L ≅ M)
    (h : (Scheme.Modules.pullbackObjUnitIso (𝟙 X)).inv ≫
      (Scheme.Modules.pullback (𝟙 X)).map s ≫ e.hom = t) :
    s ≫ (((Scheme.Modules.pullbackId X).app L).symm ≪≫ e).hom = t := by
  have he : Scheme.Modules.pullbackObjUnitIso (𝟙 X) =
      (Scheme.Modules.pullbackId X).app (SheafOfModules.unit X.ringCatSheaf) :=
    Iso.ext (Scheme.Modules.pullbackObjUnitIso_id X)
  have hu : (Scheme.Modules.pullbackId X).inv.app
      (SheafOfModules.unit X.ringCatSheaf) =
        (Scheme.Modules.pullbackObjUnitIso (𝟙 X)).inv :=
    (congrArg Iso.inv he).symm
  have hs : s ≫ (Scheme.Modules.pullbackId X).inv.app L =
      (Scheme.Modules.pullbackObjUnitIso (𝟙 X)).inv ≫
        (Scheme.Modules.pullback (𝟙 X)).map s :=
    ((Scheme.Modules.pullbackId X).inv.naturality s).trans
      (congrArg (fun a => a ≫ (Scheme.Modules.pullback (𝟙 X)).map s) hu)
  change s ≫ ((Scheme.Modules.pullbackId X).inv.app L ≫ e.hom) = t
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ e.hom) hs).trans
      ((Category.assoc _ _ _).trans h))

section Lines

variable {T J : Type u} [commT : CommRing T]
    (N F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} T)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of T) ⋙ Over.forget (Spec (.of T))) ⋙
      Scheme.forget).IsLocallyDirected]
    [hFdir : ((F.op ⋙ algSpec (.of T) ⋙ Over.forget (Spec (.of T))) ⋙
      Scheme.forget).IsLocallyDirected]
    (e : N ≅ F) (cN : Cocone (N.op ⋙ algSpec (.of T))) (hcN : IsColimit cN)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (deltaF : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (F.obj s)ˣ)
    (hd : ∀ s j hj k hk, ((matchingIsoRingMap e).app s).hom
      (deltaN s j hj k hk : N.obj s) = (deltaF s j hj k hk : F.obj s))

/-- The matching lines of isomorphic diagrams are canonically identified on
the same glued scheme, with no change of the cocone point. -/
def matchingDiagramIso (n : ℕ)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (hcoF : ∀ s j hj k hk l hl,
      deltaF s j hj l hl = deltaF s k hk l hl * deltaF s j hj k hk)
    (hnF : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (deltaF s j hj k hk) =
        deltaF t j ((leOfHom f) hj) k ((leOfHom f) hk)) :
    matchingModule N cN deltaN n ≅
      matchingModule F (matchingIsoCocone e cN) deltaF n := by
  let cF : Cocone (F.op ⋙ algSpec (.of T)) := matchingIsoCocone e cN
  let hcF : IsColimit cF := matchingIsoCoconeColimit e cN hcN
  let v := matchingIsoRingMap e
  let q : cF.pt.left ⟶ cN.pt.left := 𝟙 cN.pt.left
  have hq : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ q := matchingIsoCocone_leg e cN
  let E := @matchingPullbackIso.{u} T T J commT commT N F
    hNopen hFopen hNdir hFdir cN hcN cF hcF v q hq
    deltaN deltaF hd n hcoN hnN hcoF hnF
  exact ((Scheme.Modules.pullbackId cN.pt.left).app
    (matchingModule N cN deltaN n)).symm ≪≫ E

/-- The diagram identification preserves the coefficient matching section at
every character power. -/
theorem matchingDiagramIso_section (n : ℕ)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (hcoF : ∀ s j hj k hk l hl,
      deltaF s j hj l hl = deltaF s k hk l hl * deltaF s j hj k hk)
    (hnF : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (deltaF s j hj k hk) =
        deltaF t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (rN : ∀ j : J, N.obj (singletonIndex j))
    (rF : ∀ j : J, F.obj (singletonIndex j))
    (hrN : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom (rN j) =
        (N.map (singletonArrow s k hk)).hom (rN k) * (deltaN s j hj k hk : N.obj s))
    (hrF : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (F.map (singletonArrow s j hj)).hom (rF j) =
        (F.map (singletonArrow s k hk)).hom (rF k) * (deltaF s j hj k hk : F.obj s))
    (hv : ∀ j, ((matchingIsoRingMap e).app (singletonIndex j)).hom (rN j) = rF j) :
    coefficientMatchingSection N cN deltaN rN hrN n ≫
        (matchingDiagramIso N F e cN hcN deltaN deltaF hd n hcoN hnN hcoF hnF).hom =
      coefficientMatchingSection F (matchingIsoCocone e cN) deltaF rF hrF n := by
  let cF : Cocone (F.op ⋙ algSpec (.of T)) := matchingIsoCocone e cN
  let hcF : IsColimit cF := matchingIsoCoconeColimit e cN hcN
  let v := matchingIsoRingMap e
  let q : cF.pt.left ⟶ cN.pt.left := 𝟙 cN.pt.left
  have hq : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ q := matchingIsoCocone_leg e cN
  let E := @matchingPullbackIso.{u} T T J commT commT N F
    hNopen hFopen hNdir hFdir cN hcN cF hcF v q hq
    deltaN deltaF hd n hcoN hnN hcoF hnF
  have hs := @matchingPullbackIso_section.{u} T T J commT commT N F
    hNopen hFopen hNdir hFdir cN hcN cF hcF v q hq
    deltaN deltaF hd n hcoN hnN hcoF hnF rN rF hrN hrF hv
  exact identity_section
    (coefficientMatchingSection N cN deltaN rN hrN n)
    (coefficientMatchingSection F cF deltaF rF hrF n) E hs

end Lines

end SchubertGeometry.RetainedCharacter
