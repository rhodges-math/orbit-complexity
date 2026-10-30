import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPullback
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Polynomial section coordinates after coefficient change

The prescribed matching-line section has the mapped polynomial coordinate
under the canonical scalar pullback isomorphism. The coefficient ring may
have any characteristic, and all chart maps and coframes are retained.
-/

set_option autoImplicit false
noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting.RetainedCharacter

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private pullSection from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
open private sectionValue comparison_section section_chart_map from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendSectionCoordinates
open private comparisonCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private spec_coefficient_map from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.MatchingSections

private theorem section_inverse {C : Type*} [Category C] {A B D : C}
    (e : B ≅ D) (a : A ⟶ B) (b : A ⟶ D) (h : a ≫ e.hom = b) :
    b ≫ e.inv = a := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem polynomial_coordinate_map
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (d n : ℕ) (P : Polynomial A) (j : Fin 2) :
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial A))).inv
          (sectionChartPolynomial d (P ^ n) j)) =
      (Scheme.ΓSpecIso (.of (Polynomial B))).inv
        (sectionChartPolynomial d ((Polynomial.map f P) ^ n) j) := by
  have hm : Polynomial.map f (sectionChartPolynomial d (P ^ n) j) =
      sectionChartPolynomial d ((Polynomial.map f P) ^ n) j := by
    rw [section_chart_map, Polynomial.map_pow]
  exact (spec_coefficient_map (CommRingCat.ofHom (Polynomial.mapRingHom f)) _).trans
    (congrArg (fun z : Polynomial B => (Scheme.ΓSpecIso (.of (Polynomial B))).inv z) hm)

private theorem polynomial_section_map
    {A B : Type u} [CommRing A] [CommRing B] {X Y : Scheme.{u}}
    (q : Y ⟶ X) (k : Spec (.of (Polynomial B)) ⟶ Y)
    (r : Spec (.of (Polynomial A)) ⟶ X) (f : A →+* B)
    (h : k ≫ q = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫ r)
    (M : Y.Modules) (L : X.Modules) (E : M ≅ (Scheme.Modules.pullback q).obj L)
    (e : (Scheme.Modules.pullback r).obj L ≅ SheafOfModules.unit
      (Spec (.of (Polynomial A))).ringCatSheaf)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (hs : s ≫ E.hom = pullSection q L t)
    (d n : ℕ) (P : Polynomial A) (j : Fin 2)
    (hr : sectionValue r L t e.hom
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv
        (sectionChartPolynomial d (P ^ n) j))) :
    sectionValue k M s
      (comparisonCoframe k q
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))) r h M L E e).hom
      ((Scheme.ΓSpecIso (.of (Polynomial B))).inv
        (sectionChartPolynomial d ((Polynomial.map f P) ^ n) j)) := by
  have hv := comparison_section k q
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))) r h M L E e
    (comparisonCoframe k q
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))) r h M L E e)
    s t ((Scheme.ΓSpecIso (.of (Polynomial A))).inv
      (sectionChartPolynomial d (P ^ n) j)) rfl hs hr
  rw [polynomial_coordinate_map f d n P j] at hv
  exact hv

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
/-- The canonical matching-line pullback carries every retained polynomial
section coordinate to its coefficient image, including in positive characteristic. -/
theorem matchingSection_baseChange
    {A B : Type u} [CommRing A] [CommRing B]
    (a : Spec (.of (Polynomial A)) ⟶ cN.pt.left)
    (b : Spec (.of (Polynomial B)) ⟶ cF.pt.left) (f : A →+* B)
    (h : b ≫ q = Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫ a)
    (E : (Scheme.Modules.pullback a).obj (matchingModule N cN deltaN n) ≅
      SheafOfModules.unit (Spec (.of (Polynomial A))).ringCatSheaf)
    (d : ℕ) (P : Polynomial A) (j : Fin 2)
    (hsection : sectionValue a (matchingModule N cN deltaN n)
      (coefficientMatchingSection N cN deltaN rN hrN n) E.hom
      ((Scheme.ΓSpecIso (.of (Polynomial A))).inv
        (sectionChartPolynomial d (P ^ n) j))) :
    let e := matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n
      hcoN hnN hcoF hnF
    sectionValue b (matchingModule F cF deltaF n)
      (coefficientMatchingSection F cF deltaF rF hrF n)
      (comparisonCoframe b q
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))) a h
        (matchingModule F cF deltaF n) (matchingModule N cN deltaN n) e.symm E).hom
      ((Scheme.ΓSpecIso (.of (Polynomial B))).inv
        (sectionChartPolynomial d ((Polynomial.map f P) ^ n) j)) := by
  let e := matchingPullbackIso N F cN hcN cF hcF v q hq deltaN deltaF hd n
    hcoN hnN hcoF hnF
  have he : pullSection q (matchingModule N cN deltaN n)
      (coefficientMatchingSection N cN deltaN rN hrN n) ≫ e.hom =
        coefficientMatchingSection F cF deltaF rF hrF n :=
    matchingPullbackIso_section N F cN hcN cF hcF v q hq deltaN deltaF hd n
      hcoN hnN hcoF hnF rN rF hrN hrF hv
  have hs : coefficientMatchingSection F cF deltaF rF hrF n ≫ e.inv =
      pullSection q (matchingModule N cN deltaN n)
        (coefficientMatchingSection N cN deltaN rN hrN n) :=
    section_inverse e _ _ he
  exact polynomial_section_map q b a f h
    (matchingModule F cF deltaF n) (matchingModule N cN deltaN n) e.symm E
    (coefficientMatchingSection F cF deltaF rF hrF n)
    (coefficientMatchingSection N cN deltaN rN hrN n) hs d n P j hsection

end SchubertGeometry.RetainedCharacter
