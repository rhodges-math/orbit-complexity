import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingScalarMap
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameScalarTransport
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitTrivialization
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.IntersectionModelCover
import OrbitComplexity.FrobeniusSplitting.Modules.Sections
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Pullback of the retained character matching line

The scalar morphism of matching modules is an isomorphism: on each affine
chart it is the pullback of a unit frame. This argument applies to every scalar
map of coefficient rings and requires no flatness hypothesis. The isomorphism
carries the retained coefficient section to the same coefficient section after
scalar extension.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter

noncomputable section

universe u

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private coconeCover
  from OrbitComplexity.FrobeniusSplitting.Normality.Covers.IntersectionModelCover

private theorem selected_pullback_isIso {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (c : Cocone (N.op ⋙ algSpec (.of R))) (hc : IsColimit c)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val) :
    IsIso ((Scheme.Modules.pullback (c.ι.app (op s)).left).map
      (coordinate N c delta n j)) := by
  let : IsOpenImmersion (c.ι.app (op s)).left := (retained_prior_charts N c hc).1 s
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.restrictFunctorIsoPullback (c.ι.app (op s)).left)
    (coordinate N c delta n j)).mp
      (selectedCoordinate_isIso N c hc delta n hco hn s j hj)

private theorem singleton_chart_cover {K J : Type u} [CommRing K]
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (c : Cocone (F.op ⋙ algSpec (.of K))) (hc : IsColimit c) (x : c.pt.left) :
    ∃ (j : J) (y : Spec (.of (F.obj (singletonIndex j)))),
      (c.ι.app (op (singletonIndex j))).left y = x := by
  let D := F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))
  let C := (Over.forget (Spec (.of K))).mapCocone c
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion (D.map f) := fun f => hopen f.unop
  let hC : IsColimit C := isColimitOfPreserves (Over.forget (Spec (.of K))) hc
  let U := coconeCover D C hC
  obtain ⟨s, y, hy⟩ := U.exists_eq x
  change D.obj s at y
  change (c.ι.app (op s.unop)).left y = x at hy
  obtain ⟨j, hj⟩ := s.unop.property
  refine ⟨j, (nodeMap F c (singletonArrow s.unop j hj)).left y, ?_⟩
  exact (congrArg (fun z => z y) (nodeMap F c (singletonArrow s.unop j hj)).w).trans hy

variable {R K J : Type u} [CommRing R] [CommRing K]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
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
      (deltaF s j hj k hk : F.obj s))
    (n : ℕ)
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

include hNopen hFopen hNdir hFdir hcN hcF hcoN hnN hcoF hnF in
/-- The scalar morphism between the two specified character matching modules
is an isomorphism, as follows from their local unit frames. -/
theorem matchingPullback_isIso :
    IsIso (matchingPullbackHom N F cN cF v q hq deltaN deltaF hd n) := by
  let : ∀ s, IsOpenImmersion (cN.ι.app (op s)).left :=
    (retained_prior_charts N cN hcN).1
  let : ∀ s, IsOpenImmersion (cF.ι.app (op s)).left :=
    (retained_prior_charts F cF hcF).1
  apply @FrobeniusSplitting.isIso_on_open_family cF.pt.left J
    (fun j => Spec (.of (F.obj (singletonIndex j))))
    (fun j => (cF.ι.app (op (singletonIndex j))).left)
    (fun j => (retained_prior_charts F cF hcF).1 (singletonIndex j))
    (singleton_chart_cover F cF hcF)
  intro j
  let : IsOpenImmersion (cF.ι.app (op (singletonIndex j))).left :=
    (retained_prior_charts F cF hcF).1 (singletonIndex j)
  let : IsOpenImmersion (cN.ι.app (op (singletonIndex j))).left :=
    (retained_prior_charts N cN hcN).1 (singletonIndex j)
  have hi := frameScalar_isIso q
    (cF.ι.app (op (singletonIndex j))).left
    (cN.ι.app (op (singletonIndex j))).left
    (Spec.map (v.app (singletonIndex j))) (hq (singletonIndex j))
    (matchingModule N cN deltaN n) (matchingModule F cF deltaF n)
    (coordinate N cN deltaN n j) (coordinate F cF deltaF n j)
    (matchingPullbackHom N F cN cF v q hq deltaN deltaF hd n)
    (selected_pullback_isIso N cN hcN deltaN n hcoN hnN
      (singletonIndex j) j (Finset.mem_singleton_self j))
    (selected_pullback_isIso F cF hcF deltaF n hcoF hnF
      (singletonIndex j) j (Finset.mem_singleton_self j))
    (matchingPullbackHom_coordinate N F cN cF v q hq deltaN deltaF hd n j)
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.restrictFunctorIsoPullback
      (cF.ι.app (op (singletonIndex j))).left)
    (matchingPullbackHom N F cN cF v q hq deltaN deltaF hd n)).mpr hi

/-- The retained matching character line commutes with the specified scalar
map on the same coefficient diagrams and the same glued schemes. -/
def matchingPullbackIso :
    (Scheme.Modules.pullback q).obj (matchingModule N cN deltaN n) ≅
      matchingModule F cF deltaF n := by
  let : IsIso (matchingPullbackHom N F cN cF v q hq deltaN deltaF hd n) :=
    matchingPullback_isIso N F cN hcN cF hcF v q hq deltaN deltaF hd n hcoN hnN hcoF hnF
  exact asIso (matchingPullbackHom N F cN cF v q hq deltaN deltaF hd n)

variable
    (rN : ∀ j : J, N.obj (singletonIndex j))
    (rF : ∀ j : J, F.obj (singletonIndex j))
    (hrN : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (N.map (singletonArrow s j hj)).hom (rN j) =
        (N.map (singletonArrow s k hk)).hom (rN k) * (deltaN s j hj k hk : N.obj s))
    (hrF : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      (F.map (singletonArrow s j hj)).hom (rF j) =
        (F.map (singletonArrow s k hk)).hom (rF k) * (deltaF s j hj k hk : F.obj s))
    (hv : ∀ j, (v.app (singletonIndex j)).hom (rN j) = rF j)

include hv in
/-- The matching-line pullback isomorphism carries the retained coefficient
section to its prescribed scalar image for every character power. -/
theorem matchingPullbackIso_section :
    (Scheme.Modules.pullbackObjUnitIso q).inv ≫
        (Scheme.Modules.pullback q).map
          (coefficientMatchingSection N cN deltaN rN hrN n) ≫
        (matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n
          hcoN hnN hcoF hnF).hom =
      coefficientMatchingSection F cF deltaF rF hrF n :=
  matchingPullback_section N F cN cF v q hq deltaN deltaF hd n rN rF hrN hrF hv

end SchubertGeometry.RetainedCharacter
