import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedFrameRatios
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.CoframeAdjustmentPowers
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Matching coframe families over one coefficient extension

A retained family of degree-one units adjusts the original matching coframes
in every character power. The coefficient extension and the canonical scalar
comparison remain fixed throughout the family.
-/

set_option autoImplicit false
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits (Cocone IsColimit)
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace SchubertGeometry.RetainedCharacter

open private comparisonCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private polynomialBase from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private scalarMap adjustedFamilyData adjustments_of_units from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments

section Families

variable {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {I : Type v} (M A : I → Type u)
    [∀ l, CommRing (M l)] [∀ l, Algebra S (M l)]
    [∀ l, CommRing (A l)] [∀ l, Algebra K (A l)]
    (e : ∀ l, K ⊗[S] M l ≃ₐ[K] A l) (f : ∀ l, M l →+* A l)
    {Y YK : Scheme.{u}} (q : YK ⟶ Y) (L : ℕ → Y.Modules)
    (j : ∀ l, Spec (.of (M l)) ⟶ Y) (a : ∀ l, Spec (.of (A l)) ⟶ YK)
    (hs : ∀ l, Spec.map (CommRingCat.ofHom (f l)) ≫ j l = a l ≫ q)
    (E : ∀ n l, (Scheme.Modules.pullback (j l)).obj (L n) ≅
      SheafOfModules.unit (Spec (.of (M l))).ringCatSheaf)
    (F : ∀ n l, (Scheme.Modules.pullback (a l)).obj
      ((Scheme.Modules.pullback q).obj (L n)) ≅
        SheafOfModules.unit (Spec (.of (A l))).ringCatSheaf)

private def coframeFamilyData (d : ∀ l, (T ⊗[S] M l)ˣ) : Prop :=
  (∀ n l, scalarMap (R := T) (e l) ((d l : T ⊗[S] M l) ^ n) =
    (affineCoframeUnit (A l)
      (squareFrameIso q (a l) (j l) (Spec.map (CommRingCat.ofHom (f l)))
        (hs l) (L n) (E n l)) (F n l) : A l)) ∧
  ∀ n, adjustedFamilyData (R := T) M A e f q (L n) j a hs (E n) (F n)

private theorem families_of_units
    (he : ∀ l x, e l ((1 : K) ⊗ₜ[S] x) = f l x)
    (d : ∀ l, (T ⊗[S] M l)ˣ)
    (hd : ∀ l, scalarMap (R := T) (e l) (d l : T ⊗[S] M l) =
      (affineCoframeUnit (A l)
        (squareFrameIso q (a l) (j l) (Spec.map (CommRingCat.ofHom (f l)))
          (hs l) (L 1) (E 1 l)) (F 1 l) : A l))
    (hratio : ∀ n l, affineCoframeUnit (A l)
      (squareFrameIso q (a l) (j l) (Spec.map (CommRingCat.ofHom (f l)))
        (hs l) (L n) (E n l)) (F n l) =
      (affineCoframeUnit (A l)
        (squareFrameIso q (a l) (j l) (Spec.map (CommRingCat.ofHom (f l)))
          (hs l) (L 1) (E 1 l)) (F 1 l)) ^ n) :
    coframeFamilyData M A e f q L j a hs E F d := by
  have hpow : ∀ l n, scalarMap (R := T) (e l) ((d l : T ⊗[S] M l) ^ n) =
      (affineCoframeUnit (A l)
        (squareFrameIso q (a l) (j l) (Spec.map (CommRingCat.ofHom (f l)))
          (hs l) (L 1) (E 1 l)) (F 1 l) : A l) ^ n := by
    intro l n
    rw [map_pow, hd l]
  have hdata := adjustments_of_units (R := T) M A e f q (L 1) j a hs (E 1) (F 1)
    he d hd hpow
  obtain ⟨_, _, hall⟩ := coframeAdjustments_powers (R := T) M A e f q L j a hs E F
    he hdata hratio
  refine ⟨?_, hall⟩
  intro n l
  have hr : (affineCoframeUnit (A l)
      (squareFrameIso q (a l) (j l) (Spec.map (CommRingCat.ofHom (f l)))
        (hs l) (L n) (E n l)) (F n l) : A l) =
      (affineCoframeUnit (A l)
        (squareFrameIso q (a l) (j l) (Spec.map (CommRingCat.ofHom (f l)))
          (hs l) (L 1) (E 1 l)) (F 1 l) : A l) ^ n := by
    exact congrArg (fun x : (A l)ˣ => (x : A l)) (hratio n l)
  exact (hpow l n).trans hr.symm

end Families

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (word : List G.rootBase.support) (i : G.rootBase.support)
    (q : cF.pt.left ⟶ bsdhScheme G (word ++ [i]))
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj (op (F.obj (singletonIndex j))) ⟶
      (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (singletonIndex j))).left ≫ (q ≫ bsdhMap G (word ++ [i])))
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
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
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

/-- Retained degree-one units give adjusted coframes in every character power
on the same coefficient extension, using the canonical word-line comparisons.
The scalar images of the unit powers are included in the result. -/
theorem retainedCoframe_families
    {T : Type u} [CommRing T] [Algebra R T] [Algebra R K] [Algebra T K]
    [IsScalarTower R T K] {I : Type v}
    (M : I → Type u) [∀ l, CommRing (M l)] [∀ l, Algebra R (M l)]
    (A : I → CommAlgCat.{u} K)
    (e : ∀ l, K ⊗[R] M l ≃ₐ[K] A l) (v₀ : ∀ l, M l →+* A l)
    (he : ∀ l x, e l ((1 : K) ⊗ₜ[R] x) = v₀ l x)
    (idx : I → J)
    (t : ∀ l, Spec (.of (M l)) ⟶ Spec (.of (N.obj (singletonIndex (idx l)))))
    (f : ∀ l, (algSpec (.of K)).obj (op (A l)) ⟶
      (algSpec (.of K)).obj (op (F.obj (singletonIndex (idx l)))))
    (hs : ∀ l, Spec.map (CommRingCat.ofHom (v₀ l)) ≫ t l =
      (f l).left ≫ Spec.map (v.app (singletonIndex (idx l))))
    (hscalar : ∀ l, Spec.map (CommRingCat.ofHom (v₀ l)) ≫
      (t l ≫ (cN.ι.app (op (singletonIndex (idx l)))).left) =
      ((f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left) ≫ qN)
    (V : I → Over (Spec (.of K))) (g : I → G.points)
    (b : ∀ l, V l ⟶ (oppositeUnipotentVariety G).toOver)
    (c : ∀ l, V l ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : ∀ l, (c l).left ≫ (bsdhAppendIso G word i).hom.left ≫
      CategoryTheory.Limits.pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b l ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ (g l))
    (B : I → CommAlgCat.{u} K)
    (p : ∀ l, (algSpec (.of K)).obj (op (B l)) ⟶ V l) (ε : I → Fin 2)
    (k : ∀ l, (algSpec (.of K)).obj (op (A l)) ⟶ polynomialBase (B l))
    (h : ∀ l, ((f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left) ≫ q =
      (k l).left ≫ (projectiveLinePolynomialChart (B l) ⟨ε l⟩ ≫
        projectiveAppendChart G i (B l) (p l) (c l)))
    (d : ∀ l, (T ⊗[R] M l)ˣ) :
    let E := fun n l => frame_on_composite (t l)
      (cN.ι.app (op (singletonIndex (idx l)))).left
      (t l ≫ (cN.ι.app (op (singletonIndex (idx l)))).left) rfl
      (matchingModule N cN deltaN n)
      (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
        (singletonIndex (idx l)) (idx l) (Finset.mem_singleton_self (idx l)))
    let H := fun n l => comparisonCoframe
      ((f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left) q (k l).left
      (projectiveLinePolynomialChart (B l) ⟨ε l⟩ ≫
        projectiveAppendChart G i (B l) (p l) (c l)) (h l)
      ((pullback qN).obj (matchingModule N cN deltaN n))
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
      (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN n)
      (appendPolynomialFrame G word i (V l) (g l) (b l) (c l) (hend l)
        (B l) (p l) n ⟨ε l⟩)
    (∀ l, scalarMap (R := T) (e l) (d l : T ⊗[R] M l) =
      (affineCoframeUnit (A l)
        (squareFrameIso qN
          ((f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left)
          (t l ≫ (cN.ι.app (op (singletonIndex (idx l)))).left)
          (Spec.map (CommRingCat.ofHom (v₀ l))) (hscalar l)
          (matchingModule N cN deltaN 1) (E 1 l)) (H 1 l) : A l)) →
    coframeFamilyData (S := R) (T := T) M (fun l => A l) e v₀ qN
      (fun n => matchingModule N cN deltaN n)
      (fun l => t l ≫ (cN.ι.app (op (singletonIndex (idx l)))).left)
      (fun l => (f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left)
      hscalar E H d := by
  intro E H hdUnits
  have hratio : ∀ n l, affineCoframeUnit (A l)
      (squareFrameIso qN
        ((f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left)
        (t l ≫ (cN.ι.app (op (singletonIndex (idx l)))).left)
        (Spec.map (CommRingCat.ofHom (v₀ l))) (hscalar l)
        (matchingModule N cN deltaN n) (E n l)) (H n l) =
      (affineCoframeUnit (A l)
        (squareFrameIso qN
          ((f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left)
          (t l ≫ (cN.ι.app (op (singletonIndex (idx l)))).left)
          (Spec.map (CommRingCat.ofHom (v₀ l))) (hscalar l)
          (matchingModule N cN deltaN 1) (E 1 l)) (H 1 l)) ^ n := by
    intro n l
    exact squareCoframe_unit_power G F cF hcF word i q point a ha beta hgroup hco hn
      N v deltaN hd cN hcN qN hqN hcoN hnN (A l) (idx l) (f l) (Spec (.of (M l)))
      (t l) (Spec.map (CommRingCat.ofHom (v₀ l))) (hs l) (hscalar l)
      (V l) (g l) (b l) (c l) (hend l) (B l) (p l) (ε l) (k l) (h l) n
  have leaf := families_of_units (S := R) (T := T) M (fun l => A l) e v₀ qN
    (fun n => matchingModule N cN deltaN n)
    (fun l => t l ≫ (cN.ι.app (op (singletonIndex (idx l)))).left)
    (fun l => (f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left)
    hscalar E H he d
  exact leaf hdUnits hratio

end SchubertGeometry.RetainedCharacter
