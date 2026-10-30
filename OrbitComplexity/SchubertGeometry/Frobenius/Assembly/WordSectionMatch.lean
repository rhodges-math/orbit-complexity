import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatching
import OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# The determinant section in the character matching module

The determinant coefficients on the chosen word charts satisfy the full-character
matching equations. Their matching section is exactly the determinant section
transported by the word-character matching isomorphism.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups Opposite
open Scheme.Modules
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex singletonArrow localFunctions coefficientSection
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase

private theorem chain_coordinate {T : Type*} [Category T] {A B C D E : T}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (p : D ⟶ E)
    {s : A ⟶ D} (hs : s = f ≫ g ≫ h) {v : A ⟶ E}
    (hv : f ≫ g ≫ h ≫ p = v) : s ≫ p = v := by
  subst s
  simpa only [Category.assoc] using hv

private theorem coefficients_of_coordinates {T : Type*} [Category T]
    {A M X Y Z : T} (s : A ⟶ M) (p : M ⟶ X) (q : M ⟶ Y)
    (a : X ⟶ Z) (b : Y ⟶ Z) (d : Z ⟶ Z) (f : A ⟶ X) (g : A ⟶ Y)
    (hf : s ≫ p = f) (hg : s ≫ q = g)
    (hpq : p ≫ a = q ≫ b ≫ d) : f ≫ a = g ≫ b ≫ d := by
  rw [← hf, ← hg]
  simp only [Category.assoc, hpq]

private theorem lifted_coordinate {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (cG : Cocone (N.op ⋙ algSpec (.of R)))
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ) (n : ℕ)
    {P : cG.pt.left.Modules} (f : ∀ j : J, P ⟶ localFunctions N cG j)
    {hf : ∀ (s : {s : Finset J // s.Nonempty}) j (hj : j ∈ s.val) k (hk : k ∈ s.val),
      f j ≫ relativeFunctionsMap cG.pt.left (nodeMap N cG (singletonArrow s j hj)) =
        f k ≫ relativeFunctionsMap cG.pt.left (nodeMap N cG (singletonArrow s k hk)) ≫
          relativeFunctionsSmul cG.pt.left (node N cG s)
            (coefficientSection N cG s ((delta s j hj k hk : N.obj s) ^ n))}
    {v : P ⟶ matchingModule N cG delta n} (hv : v = lift N cG delta n f hf) (j : J) :
    v ≫ coordinate N cG delta n j = f j := by
  subst v
  exact lift_coordinate N cG delta n f hf j

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (G : ReductiveGroupData K)

section Matching

variable {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (q : cF.pt.left ⟶ bsdhScheme G word) (n : ℕ)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (.op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (.op (singletonIndex j))).left ≫ (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (.op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, chartLift G F point a s j hj =
      chartLift G F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, wordTransitionUnit G F beta s j hj l hl =
      wordTransitionUnit G F beta s k hk l hl * wordTransitionUnit G F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom (wordTransitionUnit G F beta s j hj k hk) =
        wordTransitionUnit G F beta t j ((leOfHom f) hj) k ((leOfHom f) hk))

/-- The determinant coefficient on one of the chosen word-character charts. -/
def wordMatchingCoefficient (j : J) :
    SheafOfModules.unit cF.pt.left.ringCatSheaf ⟶ localFunctions F cF j :=
  relativeCoefficient cF.pt.left (node F cF (singletonIndex j))
    ((a j ≫ flagChartMap G (point j)).left.appTop
      (DeterminantSection.positiveDetPowerFunction G n))

private theorem word_section_coordinate (j : J) :
    ((pullbackObjUnitIso q).inv ≫
      (Scheme.Modules.pullback q).map (CharacterLine.wordDeterminantModuleSection G n word) ≫
      (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn).hom) ≫
        coordinate F cF (wordTransitionUnit G F beta) n j =
      wordMatchingCoefficient G F cF n point a j :=
  chain_coordinate _ _ _ _ rfl
    (wordDeterminant_matching_coordinate G F cF hcF word q n point a ha beta hgroup hco hn j)

include hopen hdir hcF word q ha hgroup hco hn in
private theorem wordCoefficients_match
    (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (k : J) (hk : k ∈ s.val) :
    wordMatchingCoefficient G F cF n point a j ≫
        relativeFunctionsMap cF.pt.left (nodeMap F cF (singletonArrow s j hj)) =
      wordMatchingCoefficient G F cF n point a k ≫
        relativeFunctionsMap cF.pt.left (nodeMap F cF (singletonArrow s k hk)) ≫
          relativeFunctionsSmul cF.pt.left (node F cF s)
            (coefficientSection F cF s ((wordTransitionUnit G F beta s j hj k hk : F.obj s) ^ n)) :=
  coefficients_of_coordinates _ _ _ _ _ _ _ _
    (word_section_coordinate G F cF hcF word q n point a ha beta hgroup hco hn j)
    (word_section_coordinate G F cF hcF word q n point a ha beta hgroup hco hn k)
    (coordinate_matching F cF (wordTransitionUnit G F beta) n s j hj k hk)

/-- The section of the character matching module defined by its determinant
coefficients on the chosen word charts. -/
def wordMatchingSection :
    SheafOfModules.unit cF.pt.left.ringCatSheaf ⟶
      matchingModule F cF (wordTransitionUnit G F beta) n :=
  lift F cF (wordTransitionUnit G F beta) n (wordMatchingCoefficient G F cF n point a)
    (wordCoefficients_match G F cF hcF word q n point a ha beta hgroup hco hn)

/-- The matching section has the specified determinant coefficient in every chart. -/
theorem wordMatchingSection_coordinate (j : J) :
    wordMatchingSection G F cF hcF word q n point a ha beta hgroup hco hn ≫
        coordinate F cF (wordTransitionUnit G F beta) n j =
      wordMatchingCoefficient G F cF n point a j :=
  lifted_coordinate F cF (wordTransitionUnit G F beta) n
    (wordMatchingCoefficient G F cF n point a) rfl j

/-- The word determinant section is the determinant matching section under the
specified word-character isomorphism. -/
theorem wordDeterminant_section_match :
    (pullbackObjUnitIso q).inv ≫
      (Scheme.Modules.pullback q).map (CharacterLine.wordDeterminantModuleSection G n word) ≫
      (wordCharacterMatchingIso G F cF hcF word q n point a ha beta hgroup hco hn).hom =
        wordMatchingSection G F cF hcF word q n point a ha beta hgroup hco hn :=
  coordinate_hom_ext F cF (wordTransitionUnit G F beta) n _ _ (fun j =>
    (word_section_coordinate G F cF hcF word q n point a ha beta hgroup hco hn j).trans
      (wordMatchingSection_coordinate G F cF hcF word q n point a ha beta hgroup hco hn j).symm)

end Matching

end SchubertGeometry.RetainedCharacter
