import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedLocalFrames
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareComposition
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareRestriction
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Scalar matching coframes on refinements

The scalar comparison of the matching line is pulled to two commuting refined
charts. The resulting coframe remains the square coframe of the original line.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private scalarIso from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.LiftEvaluation
open private singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private theorem iso_app_refl {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (M : C) : (Iso.refl F).app M = Iso.refl (F.obj M) := rfl

private theorem iso_app_symm {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) (M : C) : e.symm.app M = (e.app M).symm := rfl

private theorem compositeFrame_rfl {X Y Z : Scheme.{u}}
    (c : X ⟶ Y) (a : Y ⟶ Z) (L : Z.Modules)
    (E : (Scheme.Modules.pullback a).obj L ≅ unitModule Y) :
    frame_on_composite c a (c ≫ a) rfl L E =
      ((pullbackComp c a).app L).symm ≪≫
        (Scheme.Modules.pullback c).mapIso E ≪≫ pullbackObjUnitIso c := by
  simp only [frame_on_composite, pullbackCongr, eqToIso_refl, iso_app_refl,
    iso_app_symm]
  exact Iso.refl_trans _

private theorem squareFrame_refine {S T A B Q P : Scheme.{u}}
    (q : T ⟶ S) (a : A ⟶ T) (b : B ⟶ S) (k : A ⟶ B)
    (h : k ≫ b = a ≫ q) (c : Q ⟶ A) (t : P ⟶ B) (u : Q ⟶ P)
    (hs : u ≫ t = c ≫ k)
    (htotal : u ≫ (t ≫ b) = (c ≫ a) ≫ q)
    (L : S.Modules) (E : (Scheme.Modules.pullback b).obj L ≅ unitModule B) :
    squareFrameIso q (c ≫ a) (t ≫ b) u htotal L
        (frame_on_composite t b (t ≫ b) rfl L E) =
      frame_on_composite c a (c ≫ a) rfl ((Scheme.Modules.pullback q).obj L)
        (squareFrameIso q a b k h L E) := by
  have h₁ : (u ≫ t) ≫ b = (c ≫ a) ≫ q := by
    simpa only [Category.assoc] using htotal
  have h₂ : (c ≫ k) ≫ b = (c ≫ a) ≫ q := by
    simpa only [hs] using h₁
  rw [compositeFrame_rfl, squareFrameIso_chart_comp q (c ≫ a) b u t htotal h₁ L E]
  have hmap : squareFrameIso q (c ≫ a) b (u ≫ t) h₁ L E =
      squareFrameIso q (c ≫ a) b (c ≫ k) h₂ L E := by
    simp only [hs]
  rw [hmap, squareFrameIso_domain_comp q a b k h c h₂ L E, compositeFrame_rfl]

private theorem compositeFrame_map {T A Q : Scheme.{u}}
    (c : Q ⟶ A) (a : A ⟶ T) (L M : T.Modules) (I : L ≅ M)
    (E : (Scheme.Modules.pullback a).obj M ≅ unitModule A) :
    (Scheme.Modules.pullback (c ≫ a)).mapIso I ≪≫
        frame_on_composite c a (c ≫ a) rfl M E =
      frame_on_composite c a (c ≫ a) rfl L
        ((Scheme.Modules.pullback a).mapIso I ≪≫ E) := by
  rw [compositeFrame_rfl, compositeFrame_rfl]
  have hn : (Scheme.Modules.pullback (c ≫ a)).mapIso I ≪≫
      (pullbackComp c a).symm.app M =
      (pullbackComp c a).symm.app L ≪≫
        (Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback c).mapIso I := by
    apply Iso.ext
    exact (pullbackComp c a).inv.naturality I.hom
  have hp := congrArg (fun E' => E' ≪≫ (Scheme.Modules.pullback c).mapIso E ≪≫
    pullbackObjUnitIso c) hn
  have hf : (Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback c).mapIso I =
      (Scheme.Modules.pullback c).mapIso ((Scheme.Modules.pullback a).mapIso I) := rfl
  simpa only [iso_app_symm, hf, CategoryTheory.Functor.mapIso_trans, Iso.trans_assoc] using hp

private theorem refinedFrame_of_node {S T A B Q P : Scheme.{u}}
    (q : T ⟶ S) (a : A ⟶ T) (b : B ⟶ S) (k : A ⟶ B)
    (h : k ≫ b = a ≫ q) (c : Q ⟶ A) (t : P ⟶ B) (u : Q ⟶ P)
    (hs : u ≫ t = c ≫ k)
    (htotal : u ≫ (t ≫ b) = (c ≫ a) ≫ q)
    (L : S.Modules) (M : T.Modules) (I : (Scheme.Modules.pullback q).obj L ≅ M)
    (E : (Scheme.Modules.pullback b).obj L ≅ unitModule B)
    (F : (Scheme.Modules.pullback a).obj M ≅ unitModule A)
    (hnode : (Scheme.Modules.pullback a).mapIso I ≪≫ F =
      squareFrameIso q a b k h L E) :
    (Scheme.Modules.pullback (c ≫ a)).mapIso I ≪≫
        frame_on_composite c a (c ≫ a) rfl M F =
      squareFrameIso q (c ≫ a) (t ≫ b) u htotal L
        (frame_on_composite t b (t ≫ b) rfl L E) := by
  rw [compositeFrame_map, hnode]
  exact (squareFrame_refine q a b k h c t u hs htotal L E).symm

section Matching

variable {R K J : Type u} [CommRing R] [CommRing K]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    [((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (q : cF.pt.left ⟶ cN.pt.left)
    (hq : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ q)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (deltaF : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (F.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (deltaF s j hj k hk : F.obj s)) (n : ℕ)
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

private theorem scalarIso_one {X : Scheme.{u}} (M : X.Modules) :
    scalarIso M 1 = Iso.refl M := by
  apply Iso.ext
  exact globalSectionsSmul_one M

private theorem iso_scalar_one {X : Scheme.{u}} (L M : X.Modules) (E : L ≅ M) :
    E ≪≫ scalarIso M 1 = E :=
  (congrArg (fun F : M ≅ M => E ≪≫ F) (scalarIso_one M)).trans (Iso.trans_refl E)

private theorem retainedUnitFrame_one (j : J) :
    retainedUnitFrame N cN hcN deltaN n hcoN hnN j 1 =
      localCharacterTrivialization N cN hcN deltaN n hcoN hnN
        (singletonIndex j) j (Finset.mem_singleton_self j) := by
  simp only [retainedUnitFrame, one_pow, map_one]
  exact iso_scalar_one _ _ _

private theorem nodeFrame_scalar (j : J) :
    (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex j))).left).mapIso
        (matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n
          hcoN hnN hcoF hnF) ≪≫
      localCharacterTrivialization F cF hcF deltaF n hcoF hnF
        (singletonIndex j) j (Finset.mem_singleton_self j) =
      squareFrameIso q (cF.ι.app (op (singletonIndex j))).left
        (cN.ι.app (op (singletonIndex j))).left (Spec.map (v.app (singletonIndex j)))
        (hq (singletonIndex j)) (matchingModule N cN deltaN n)
        (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
          (singletonIndex j) j (Finset.mem_singleton_self j)) := by
  have h := retainedUnitFrame_scalar N F cN hcN cF hcF v q hq deltaN deltaF hd n
    hcoN hnN hcoF hnF j 1 1 ((v.app (singletonIndex j)).hom.map_one)
  have he : (Scheme.Modules.pullback (cF.ι.app (op (singletonIndex j))).left).mapIso
        (matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n
          hcoN hnN hcoF hnF) ≪≫
      retainedUnitFrame F cF hcF deltaF n hcoF hnF j 1 =
      squareFrameIso q (cF.ι.app (op (singletonIndex j))).left
        (cN.ι.app (op (singletonIndex j))).left (Spec.map (v.app (singletonIndex j)))
        (hq (singletonIndex j)) (matchingModule N cN deltaN n)
        (retainedUnitFrame N cN hcN deltaN n hcoN hnN j 1) := by
    apply Iso.ext
    exact h
  simpa only [retainedUnitFrame_one] using he

/-- The canonical matching-line scalar comparison respects coframes on any two
commuting refinements of a singleton chart. The matching modules and their
comparison isomorphism are unchanged. -/
theorem refinedUnitFrame_scalar (j : J) {Q P : Scheme.{u}}
    (c : Q ⟶ Spec (.of (F.obj (singletonIndex j))))
    (t : P ⟶ Spec (.of (N.obj (singletonIndex j)))) (u : Q ⟶ P)
    (hs : u ≫ t = c ≫ Spec.map (v.app (singletonIndex j)))
    (htotal : u ≫ (t ≫ (cN.ι.app (op (singletonIndex j))).left) =
      (c ≫ (cF.ι.app (op (singletonIndex j))).left) ≫ q) :
    (Scheme.Modules.pullback (c ≫ (cF.ι.app (op (singletonIndex j))).left)).mapIso
        (matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n
          hcoN hnN hcoF hnF) ≪≫
      frame_on_composite c (cF.ι.app (op (singletonIndex j))).left
        (c ≫ (cF.ι.app (op (singletonIndex j))).left) rfl (matchingModule F cF deltaF n)
        (localCharacterTrivialization F cF hcF deltaF n hcoF hnF
          (singletonIndex j) j (Finset.mem_singleton_self j)) =
      squareFrameIso q (c ≫ (cF.ι.app (op (singletonIndex j))).left)
        (t ≫ (cN.ι.app (op (singletonIndex j))).left) u htotal
        (matchingModule N cN deltaN n)
        (frame_on_composite t (cN.ι.app (op (singletonIndex j))).left
          (t ≫ (cN.ι.app (op (singletonIndex j))).left) rfl (matchingModule N cN deltaN n)
          (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
            (singletonIndex j) j (Finset.mem_singleton_self j))) := by
  exact refinedFrame_of_node q (cF.ι.app (op (singletonIndex j))).left
    (cN.ι.app (op (singletonIndex j))).left (Spec.map (v.app (singletonIndex j)))
    (hq (singletonIndex j)) c t u hs htotal (matchingModule N cN deltaN n)
    (matchingModule F cF deltaF n)
    (matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n hcoN hnN hcoF hnF)
    _ _ (nodeFrame_scalar N F cN hcN cF hcF v q hq deltaN deltaF hd n hcoN hnN hcoF hnF j)

end Matching

end SchubertGeometry.RetainedCharacter
