import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCoefficientDescent
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# The arithmetic cocycle line and the word character line

The scalar comparison for the retained matching line and the word character
comparison have the same target. Their composite identifies the two lines and
carries the retained determinant section to the word determinant section.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace SchubertGeometry.RetainedCharacter

private theorem compare_iso_sections {C : Type*} [Category C]
    {O U V A B L : C} (e : A ≅ L) (f : B ≅ L) (d : A ≅ B)
    (hd : d = e ≪≫ f.symm) (x : O ⟶ U) (s : U ⟶ A) (y : O ⟶ V) (t : V ⟶ B)
    (h : x ≫ s ≫ e.hom = y ≫ t ≫ f.hom) : x ≫ s ≫ d.hom = y ≫ t := by
  cases hd
  calc
    x ≫ s ≫ (e ≪≫ f.symm).hom = (x ≫ s ≫ e.hom) ≫ f.inv := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    _ = (y ≫ t ≫ f.hom) ≫ f.inv := congrArg (fun z => z ≫ f.inv) h
    _ = y ≫ t := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

open private singletonIndex
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    {R : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))

/-- The retained full-character matching line and the word character line
identify after pullback to their specified comparison scheme. -/
def retainedWordLineIso (n : ℕ) :
    (Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n) ≅
      (Scheme.Modules.pullback q).obj
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word) :=
  matchingPullbackIso N F cN hcN cF hcF v qN hqN deltaN
      (wordTransitionUnit G F beta) hd n hcoN hnN hco hn ≪≫
    (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn).symm

variable
    (hv : ∀ s, Function.Injective (v.app s).hom)
    (P : ∀ s : {s : Finset J // s.Nonempty}, Polynomial (N.obj s))
    (hP : ∀ j, (v.app (singletonIndex j)).hom ((P (singletonIndex j)).coeff 2) =
      wordRingCoefficient G F point a j)

/-- The line identification carries the retained polynomial section to the
word determinant section for every integral character power. -/
theorem retainedWordLineIso_section (n : ℕ) :
    (Scheme.Modules.pullbackObjUnitIso qN).inv ≫
        (Scheme.Modules.pullback qN).map
          (retainedWordSection G F cF hcF word q point a ha beta hgroup hco hn
            N v hv deltaN hd P hP cN n) ≫
        (retainedWordLineIso G F cF hcF word q point a ha beta hgroup hco hn
          N v deltaN hd cN hcN qN hqN hcoN hnN n).hom =
      (Scheme.Modules.pullbackObjUnitIso q).inv ≫
        (Scheme.Modules.pullback q).map (CharacterLine.wordDeterminantModuleSection G n word) :=
  compare_iso_sections
    (matchingPullbackIso N F cN hcN cF hcF v qN hqN deltaN
      (wordTransitionUnit G F beta) hd n hcoN hnN hco hn)
    (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn)
    (retainedWordLineIso G F cF hcF word q point a ha beta hgroup hco hn
      N v deltaN hd cN hcN qN hqN hcoN hnN n) rfl
    (Scheme.Modules.pullbackObjUnitIso qN).inv
    ((Scheme.Modules.pullback qN).map
      (retainedWordSection G F cF hcF word q point a ha beta hgroup hco hn
        N v hv deltaN hd P hP cN n))
    (Scheme.Modules.pullbackObjUnitIso q).inv
    ((Scheme.Modules.pullback q).map (CharacterLine.wordDeterminantModuleSection G n word))
    (retainedWord_section_match G F cF hcF word q point a ha beta hgroup hco hn
      N v hv deltaN hd P hP cN hcN qN hqN hcoN hnN n)

end SchubertGeometry.RetainedCharacter
