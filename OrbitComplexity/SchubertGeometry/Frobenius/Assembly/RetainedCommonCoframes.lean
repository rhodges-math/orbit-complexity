import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonMatchingCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCoframeTransport
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.ScalarColimitSquares
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPolynomialBase
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Retained common-chart matching coframes

The degree-one units on the common matching charts give the canonical
coframe family in every character power, over their original coefficient
extension. Cartesian singleton comparisons construct the field refinements.
-/

set_option autoImplicit false
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private affine_fibre_product from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameCoverRefinement
open private frame_on_composite compared_append_frame append_frame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private comparisonCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private comparedFrame_eq from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCoframeTransport
open private scalarMap adjustedFamilyData from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private coframeFamilyData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCoframeFamilies
open private matchingRefinementFrame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingAppendCoframes
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private polynomialBase from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates

private theorem image_refinement
    {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {I : Type v} (M A : I → Type u)
    [∀ l, CommRing (M l)] [∀ l, Algebra S (M l)]
    [∀ l, CommRing (A l)] [∀ l, Algebra K (A l)]
    (e : ∀ l, K ⊗[S] M l ≃ₐ[K] A l) (v₀ : ∀ l, M l →+* A l)
    {Y YK Z : Scheme.{u}} (q : YK ⟶ Y) (r : YK ⟶ Z)
    (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback q).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (D C : I → Scheme.{u}) (legN : ∀ l, D l ⟶ Y) (legF : ∀ l, C l ⟶ YK)
    (t : ∀ l, Spec (.of (M l)) ⟶ D l) (f : ∀ l, Spec (.of (A l)) ⟶ C l)
    (j : ∀ l, Spec (.of (M l)) ⟶ Y) (a : ∀ l, Spec (.of (A l)) ⟶ YK)
    (hj : ∀ l, j l = t l ≫ legN l) (ha : ∀ l, a l = f l ≫ legF l)
    (hs : ∀ l, Spec.map (CommRingCat.ofHom (v₀ l)) ≫ j l = a l ≫ q)
    (hs' : ∀ l, Spec.map (CommRingCat.ofHom (v₀ l)) ≫ (t l ≫ legN l) =
      (f l ≫ legF l) ≫ q)
    (P : I → Scheme.{u}) (k : ∀ l, Spec (.of (A l)) ⟶ P l)
    (c : ∀ l, P l ⟶ Z) (h : ∀ l, a l ≫ r = k l ≫ c l)
    (h' : ∀ l, (f l ≫ legF l) ≫ r = k l ≫ c l)
    (E : ∀ l, (Scheme.Modules.pullback (legN l)).obj L ≅
      SheafOfModules.unit (D l).ringCatSheaf)
    (F : ∀ l, (Scheme.Modules.pullback (c l)).obj LK ≅
      SheafOfModules.unit (P l).ringCatSheaf)
    (d : ∀ l, (T ⊗[S] M l)ˣ)
    (hd : ∀ l, scalarMap (R := T) (e l) (d l : T ⊗[S] M l) =
      (affineCoframeUnit (A l)
        (squareFrameIso q (a l) (j l) (Spec.map (CommRingCat.ofHom (v₀ l))) (hs l) L
          (frame_on_composite (t l) (legN l) (j l) (hj l) L (E l)))
        (compared_append_frame q r (a l) L LK EL (k l) (c l) (h l) (F l)) : A l)) :
    ∀ l, scalarMap (R := T) (e l) (d l : T ⊗[S] M l) =
      (affineCoframeUnit (A l)
        (squareFrameIso q (f l ≫ legF l) (t l ≫ legN l)
          (Spec.map (CommRingCat.ofHom (v₀ l))) (hs' l) L
          (frame_on_composite (t l) (legN l) (t l ≫ legN l) rfl L (E l)))
        (comparisonCoframe (f l ≫ legF l) r (k l) (c l) (h' l)
          ((Scheme.Modules.pullback q).obj L) LK EL (F l)) : A l) := by
  cases funext hj
  cases funext ha
  simpa only [comparedFrame_eq] using hd

private theorem affineChart_base {K : Type u} [CommRing K]
    {X : Scheme.{u}} [IsAffine X] (base : X ⟶ Spec (.of K)) :
    let : Algebra K Γ(X, ⊤) :=
      (base.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    X.isoSpec.inv ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) := by
  let : Algebra K Γ(X, ⊤) :=
    (base.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  change X.isoSpec.inv ≫ base =
    Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ base.appTop)
  rw [Spec.map_comp]
  simpa only [Scheme.isoSpec_Spec_inv] using
    (Scheme.isoSpec_inv_naturality base).symm

private theorem affineChart_over {K : Type u} [CommRing K]
    {X Y : Scheme.{u}} [IsAffine X]
    (base : Y ⟶ Spec (.of K)) (n : X ⟶ Y) :
    let : Algebra K Γ(X, ⊤) :=
      ((n ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∃ f : (algSpec (.of K)).obj (op (CommAlgCat.of K Γ(X, ⊤))) ⟶ Over.mk base,
      f.left = X.isoSpec.inv ≫ n := by
  let : Algebra K Γ(X, ⊤) :=
    ((n ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  refine ⟨Over.homMk (X.isoSpec.inv ≫ n) ?_, rfl⟩
  exact (Category.assoc _ _ _).trans (affineChart_base (n ≫ base))

private theorem singleton_lift {K : Type u} [CommRing K]
    {X D Y : Scheme.{u}} (baseX : X ⟶ Spec (.of K))
    (B Z : Over (Spec (.of K))) (b : B.left ⟶ D) (legF : B ⟶ Z)
    (legN : D ⟶ Y) (q : Z.left ⟶ Y)
    (hlocal : IsPullback b legF.left legN q)
    (a : Over.mk baseX ⟶ Z) (t : X ⟶ D) (h : t ≫ legN = a.left ≫ q) :
    ∃ f : Over.mk baseX ⟶ B, f.left ≫ b = t ∧ f.left ≫ legF.left = a.left := by
  let k := hlocal.lift t a.left h
  have hk : k ≫ legF.left = a.left := hlocal.lift_snd t a.left h
  have hb : k ≫ B.hom = baseX := by
    calc
      k ≫ B.hom = k ≫ (legF.left ≫ Z.hom) := congrArg (fun g => k ≫ g) legF.w.symm
      _ = (k ≫ legF.left) ≫ Z.hom := (Category.assoc _ _ _).symm
      _ = a.left ≫ Z.hom := congrArg (fun g => g ≫ Z.hom) hk
      _ = baseX := a.w
  exact ⟨Over.homMk k hb, hlocal.lift_fst t a.left h, hk⟩

private theorem overMap_base {K : Type u} [CommRing K]
    (W B Z : Over (Spec (.of K))) (f : W.left ⟶ B.left) (g : B ⟶ Z) (a : W ⟶ Z)
    (h : f ≫ g.left = a.left) : f ≫ B.hom = W.hom := by
  calc
    f ≫ B.hom = f ≫ (g.left ≫ Z.hom) := congrArg (fun t => f ≫ t) g.w.symm
    _ = (f ≫ g.left) ≫ Z.hom := (Category.assoc _ _ _).symm
    _ = a.left ≫ Z.hom := congrArg (fun t => t ≫ Z.hom) h
    _ = W.hom := a.w

private theorem uliftFamily_rec {I : Type v} (P : (I → ULift.{u} (Fin 2)) → Prop)
    (h : ∀ e : I → Fin 2, P (fun l => ⟨e l⟩)) : ∀ e, P e := by
  intro e
  have he : (fun l => (⟨(e l).down⟩ : ULift.{u} (Fin 2))) = e := by
    funext l
    cases e l
    rfl
  exact he ▸ h (fun l => (e l).down)

private theorem refined_triangle {X A B Y Z : Scheme.{u}}
    (v : X ⟶ A) (t : A ⟶ B) (legN : B ⟶ Y) (j : A ⟶ Y)
    (a : X ⟶ Z) (q : Z ⟶ Y) (hj : j = t ≫ legN) (hs : v ≫ j = a ≫ q) :
    (v ≫ t) ≫ legN = a ≫ q :=
  (Category.assoc _ _ _).trans ((congrArg (fun z => v ≫ z) hj.symm).trans hs)

private theorem refined_outer {X A B Y Z : Scheme.{u}}
    (v : X ⟶ A) (t : A ⟶ B) (legN : B ⟶ Y) (j : A ⟶ Y)
    {C : Scheme.{u}} (f : X ⟶ C) (legF : C ⟶ Z) (a : X ⟶ Z) (q : Z ⟶ Y)
    (hj : j = t ≫ legN) (ha : a = f ≫ legF) (hs : v ≫ j = a ≫ q) :
    v ≫ (t ≫ legN) = (f ≫ legF) ≫ q := by
  simpa only [← hj, ← ha] using hs

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
    (S : Subalgebra ℤ K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected]
    (v : N ⋙ forget₂ (CommAlgCat S) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (wordTransitionUnit G F beta s j hj k hk : F.obj s))
    (cN : Cocone (N.op ⋙ algSpec (.of S))) (hcN : IsColimit cN)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))

section Charts

variable {I : Type v} (M A : I → Type u)
    [∀ l, CommRing (M l)] [∀ l, Algebra S (M l)]
    [∀ l, CommRing (A l)] [∀ l, Algebra K (A l)]
    (e : ∀ l, K ⊗[S] M l ≃ₐ[K] A l)
    (j : ∀ l, Spec (.of (M l)) ⟶ cN.pt.left)
    (jF : ∀ l, Spec (.of (A l)) ⟶ cF.pt.left)
    (hscalar : ∀ l, Spec.map (CommRingCat.ofHom
      ((e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ j l = jF l ≫ qN)
    (idx : I → J)
    (small : ∀ l, Spec (.of (M l)) ⟶ Spec (.of (N.obj (singletonIndex (idx l)))))
    (hsmall : ∀ l, j l = small l ≫ (cN.ι.app (op (singletonIndex (idx l)))).left)
    (V₀ : I → Over (Spec (.of K))) (g : I → G.points)
    (a₀ : ∀ l, V₀ l ⟶ (oppositeUnipotentVariety G).toOver)
    (c : ∀ l, V₀ l ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : ∀ l, (c l).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a₀ l ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫ flagBundleChart G _ (g l))
    (B : I → CommAlgCat.{u} K)
    (p : ∀ l, (algSpec (.of K)).obj (op (B l)) ⟶ V₀ l)
    (ε : I → ULift.{u} (Fin 2))
    (k : ∀ l, Spec (.of (A l)) ⟶ Spec (.of (Polynomial (B l))))
    (hk : ∀ l, jF l ≫ q = k l ≫ projectiveLinePolynomialChart (B l) (ε l) ≫
      projectiveAppendChart G i (B l) (p l) (c l))

private def stageFamilyData (T : Subalgebra ℤ K) (hST : S ≤ T) : Prop :=
  letI : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  letI : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let E := fun n l => frame_on_composite (small l)
    (cN.ι.app (op (singletonIndex (idx l)))).left (j l) (hsmall l)
    (matchingModule N cN deltaN n)
    (localCharacterTrivialization N cN hcN deltaN n hcoN hnN
      (singletonIndex (idx l)) (idx l) (Finset.mem_singleton_self (idx l)))
  let H := fun n l => compared_append_frame qN q (jF l) (matchingModule N cN deltaN n)
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
    (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
      N v deltaN hd cN hcN qN hqN hcoN hnN n) (k l)
    (projectiveLinePolynomialChart (B l) (ε l) ≫ projectiveAppendChart G i (B l) (p l) (c l))
    (hk l) (appendPolynomialFrame G word i (V₀ l) (g l) (a₀ l) (c l) (hend l)
      (B l) (p l) n (ε l))
  T.FG ∧ ∃ d : ∀ l, (T ⊗[S] M l)ˣ,
    coframeFamilyData (S := S) (T := T) M A e
      (fun l => (e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
      qN (fun n => matchingModule N cN deltaN n) j jF hscalar E H d

private theorem stage_family
    (hqBase : q ≫ bsdhToSpec G (word ++ [i]) = cF.pt.hom)
    (hlocal : ∀ z : J, IsPullback (Spec.map (v.app (singletonIndex z)))
      (cF.ι.app (op (singletonIndex z))).left
      (cN.ι.app (op (singletonIndex z))).left qN)
    (aOver : ∀ l, (algSpec (.of K)).obj (op (CommAlgCat.of K (A l))) ⟶ cF.pt)
    (haOver : ∀ l, (aOver l).left = jF l)
    (hpoly : ∀ l (z : ULift.{u} (Fin 2)),
      (projectiveLinePolynomialChart (B l) z ≫
        projectiveAppendChart G i (B l) (p l) (c l)) ≫ bsdhToSpec G (word ++ [i]) =
          (polynomialBase (B l)).hom)
    (T : Subalgebra ℤ K) (hST : S ≤ T)
    (hStage : matchingAppendCoframeStage G word i S N cN hcN deltaN hcoN hnN M A e qN q
      (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN 1)
      j jF hscalar idx small hsmall V₀ g a₀ c hend B p ε k hk T hST) :
    stageFamilyData G F cF hcF word i q point a ha beta hgroup hco hn S N v deltaN hd
      cN hcN qN hqN hcoN hnN M A e j jF hscalar idx small hsmall
      V₀ g a₀ c hend B p ε k hk T hST := by
  classical
  revert hStage
  revert hk
  revert ε
  apply uliftFamily_rec
  intro eps hk hStage
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  unfold stageFamilyData
  intro E H
  let v₀ := fun l => (e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  change T.FG ∧ adjustedFamilyData (R := T) M A e v₀ qN
    (matchingModule N cN deltaN 1) j jF hscalar (E 1) (H 1) at hStage
  rcases hStage with ⟨hFG, d, hdUnits, _, _⟩
  have hLift (l : I) := singleton_lift
    ((algSpec (.of K)).obj (op (CommAlgCat.of K (A l)))).hom
    ((algSpec (.of K)).obj (op (F.obj (singletonIndex (idx l))))) cF.pt
    (Spec.map (v.app (singletonIndex (idx l))))
    (cF.ι.app (op (singletonIndex (idx l))))
    (cN.ι.app (op (singletonIndex (idx l)))).left qN (hlocal (idx l)) (aOver l)
    (Spec.map (CommRingCat.ofHom (v₀ l)) ≫ small l)
    ((refined_triangle _ _ _ _ _ _ (hsmall l) (hscalar l)).trans
      (congrArg (fun z => z ≫ qN) (haOver l).symm))
  choose f hf₀ hf₁ using hLift
  have hfOld (l : I) : (f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left = jF l :=
    (hf₁ l).trans (haOver l)
  have hOuter (l : I) : Spec.map (CommRingCat.ofHom (v₀ l)) ≫
      (small l ≫ (cN.ι.app (op (singletonIndex (idx l)))).left) =
      ((f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left) ≫ qN :=
    refined_outer _ _ _ _ _ _ _ _ (hsmall l) (hfOld l).symm (hscalar l)
  let qOver : cF.pt ⟶ Over.mk (bsdhToSpec G (word ++ [i])) := Over.homMk q hqBase
  let polyOver (l : I) : polynomialBase (B l) ⟶ Over.mk (bsdhToSpec G (word ++ [i])) :=
    Over.homMk (projectiveLinePolynomialChart (B l) ⟨eps l⟩ ≫
      projectiveAppendChart G i (B l) (p l) (c l)) (hpoly l ⟨eps l⟩)
  have hFactor (l : I) : k l ≫ (polyOver l).left = (aOver l ≫ qOver).left :=
    (hk l).symm.trans (congrArg (fun z => z ≫ q) (haOver l).symm)
  let kOver (l : I) : (algSpec (.of K)).obj (op (CommAlgCat.of K (A l))) ⟶
      polynomialBase (B l) :=
    Over.homMk (k l) (overMap_base
      ((algSpec (.of K)).obj (op (CommAlgCat.of K (A l))))
      (polynomialBase (B l)) (Over.mk (bsdhToSpec G (word ++ [i])))
      (k l) (polyOver l) (aOver l ≫ qOver) (hFactor l))
  have hWord (l : I) :
      ((f l).left ≫ (cF.ι.app (op (singletonIndex (idx l)))).left) ≫ q =
      (kOver l).left ≫ (projectiveLinePolynomialChart (B l) ⟨eps l⟩ ≫
        projectiveAppendChart G i (B l) (p l) (c l)) :=
    (congrArg (fun z => z ≫ q) (hfOld l)).trans (hk l)
  have hdCanonical := image_refinement (S := S) (T := T) M A e v₀ qN q
    (matchingModule N cN deltaN 1)
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) (word ++ [i]))
    (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
      N v deltaN hd cN hcN qN hqN hcoN hnN 1)
    (fun l => Spec (.of (N.obj (singletonIndex (idx l)))))
    (fun l => Spec (.of (F.obj (singletonIndex (idx l)))))
    (fun l => (cN.ι.app (op (singletonIndex (idx l)))).left)
    (fun l => (cF.ι.app (op (singletonIndex (idx l)))).left)
    small (fun l => (f l).left) j jF hsmall (fun l => (hfOld l).symm) hscalar hOuter
    (fun l => Spec (.of (Polynomial (B l)))) k
    (fun l => projectiveLinePolynomialChart (B l) ⟨eps l⟩ ≫
      projectiveAppendChart G i (B l) (p l) (c l)) hk hWord
    (fun l => localCharacterTrivialization N cN hcN deltaN 1 hcoN hnN
      (singletonIndex (idx l)) (idx l) (Finset.mem_singleton_self (idx l)))
    (fun l => appendPolynomialFrame G word i (V₀ l) (g l) (a₀ l) (c l) (hend l)
      (B l) (p l) 1 ⟨eps l⟩) d hdUnits
  have he (l : I) (x : M l) : e l ((1 : K) ⊗ₜ[S] x) = v₀ l x := rfl
  have hCanon := retainedCoframe_families (R := S) (T := T)
    G F cF hcF word i q point a ha beta hgroup hco hn N v deltaN hd cN hcN qN hqN hcoN hnN
    M (fun l => CommAlgCat.of K (A l)) e v₀ he idx small f
    (fun l => (hf₀ l).symm) hOuter V₀ g a₀ c hend B p eps kOver hWord d hdCanonical
  have hTransport := coframeFamily_refinement (S := S) (T := T) M A e v₀ qN q
    (fun n => matchingModule N cN deltaN n)
    (fun n => CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
    (fun n => retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
      N v deltaN hd cN hcN qN hqN hcoN hnN n)
    (fun l => Spec (.of (N.obj (singletonIndex (idx l)))))
    (fun l => Spec (.of (F.obj (singletonIndex (idx l)))))
    (fun l => (cN.ι.app (op (singletonIndex (idx l)))).left)
    (fun l => (cF.ι.app (op (singletonIndex (idx l)))).left)
    small (fun l => (f l).left) j jF hsmall (fun l => (hfOld l).symm) hscalar hOuter
    (fun l => Spec (.of (Polynomial (B l)))) k
    (fun l => projectiveLinePolynomialChart (B l) ⟨eps l⟩ ≫
      projectiveAppendChart G i (B l) (p l) (c l)) hk hWord
    (fun n l => localCharacterTrivialization N cN hcN deltaN n hcoN hnN
      (singletonIndex (idx l)) (idx l) (Finset.mem_singleton_self (idx l)))
    (fun n l => appendPolynomialFrame G word i (V₀ l) (g l) (a₀ l) (c l) (hend l)
      (B l) (p l) n ⟨eps l⟩) d
  exact ⟨hFG, d, hTransport.mpr hCanon⟩

end Charts

section Common

variable [Finite J] [cN.pt.left.IsSeparated]
    (hK : IsPullback qN cF.pt.hom cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (V : cN.pt.left.OpenCover.{u}) [Finite V.I₀] [∀ z, IsAffine (V.X z)]
    (V₀ : V.I₀ → Over (Spec (.of K))) (g : V.I₀ → G.points)
    (a₀ : ∀ z, V₀ z ⟶ (oppositeUnipotentVariety G).toOver)
    (c : ∀ z, V₀ z ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : ∀ z, (c z).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a₀ z ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫ flagBundleChart G _ (g z))
    (B : V.I₀ → CommAlgCat.{u} K)
    (p : ∀ z, (algSpec (.of K)).obj (op (B z)) ⟶ V₀ z)
    (ε : V.I₀ → ULift.{u} (Fin 2))
    (π : ∀ z, Spec (.of (Polynomial (B z))) ⟶ V.X z)
    (jK : ∀ z, Spec (.of (Polynomial (B z))) ⟶ cF.pt.left)

/-- The common coordinates retain one family of unit powers and adjusted
coframes for the canonical matching-line comparisons in every degree. -/
def commonMatchingCoframeFamilyData (T : Subalgebra ℤ K) (hST : S ≤ T) : Prop :=
  let W := matchingSingletonCover N cN hcN
  let C := appendCommonCover W V
  let : Finite W.I₀ := inferInstanceAs (Finite J)
  let : ∀ w, IsAffine (W.X w) := fun w =>
    inferInstanceAs (IsAffine (Spec (.of (N.obj (singletonIndex w)))))
  let : ∀ l, IsAffine (C.X l) := fun l => by
    let : IsAffine (W.X l.1) := inferInstance
    let : IsAffine (V.X l.2) := (inferInstance : ∀ z, IsAffine (V.X z)) l.2
    exact affine_fibre_product (W.f l.1) (V.f l.2)
  let : IsAffineHom qN := MorphismProperty.of_isPullback hK.flip inferInstance
  let P := fun l : C.I₀ => pullback (C.f l) qN
  let : ∀ l, IsAffine (P l) := fun l => inferInstance
  let M : C.I₀ → Type u := fun l => Γ(C.X l, ⊤)
  let A : C.I₀ → Type u := fun l => Γ(P l, ⊤)
  let : ∀ l, Algebra S (M l) := fun l =>
    ((C.f l ≫ cN.pt.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : ∀ l, Algebra K (A l) := fun l =>
    ((pullback.snd (C.f l) qN ≫ cF.pt.hom).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let j := fun l : C.I₀ => (C.X l).isoSpec.inv ≫ C.f l
  let jF := fun l : C.I₀ => (P l).isoSpec.inv ≫ pullback.snd (C.f l) qN
  ∃ (small : ∀ l : C.I₀, Spec (.of (M l)) ⟶ W.X l.1)
    (kN : ∀ l : C.I₀, Spec (.of (M l)) ⟶ V.X l.2)
    (kF : ∀ l : C.I₀, Spec (.of (A l)) ⟶ Spec (.of (Polynomial (B l.2))))
    (e : ∀ l : C.I₀, K ⊗[S] M l ≃ₐ[K] A l)
    (hscalar : ∀ l, Spec.map (CommRingCat.ofHom
      ((e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ j l = jF l ≫ qN)
    (hsmall : ∀ l, j l = small l ≫ (cN.ι.app (op (singletonIndex l.1))).left)
    (hk : ∀ l, jF l ≫ q = kF l ≫ projectiveLinePolynomialChart (B l.2) (ε l.2) ≫
      projectiveAppendChart G i (B l.2) (p l.2) (c l.2)),
    (∀ l, kN l ≫ V.f l.2 = j l) ∧
    (∀ l, Spec.map (pullback.fst (C.f l) qN).appTop ≫ kN l = kF l ≫ π l.2) ∧
    (∀ l, kF l ≫ jK l.2 = jF l) ∧
    (∀ l k x, e l (k ⊗ₜ[S] x) =
      algebraMap K (A l) k * (pullback.fst (C.f l) qN).appTop.hom x) ∧
    (∀ l, Module.Flat S (M l)) ∧ (∀ l, Algebra.FinitePresentation S (M l)) ∧
    stageFamilyData G F cF hcF word i q point a ha beta hgroup hco hn S N v deltaN hd
      cN hcN qN hqN hcoN hnN M A e j jF hscalar (fun l => l.1) small hsmall
      (fun l => V₀ l.2) (fun l => g l.2) (fun l => a₀ l.2) (fun l => c l.2)
      (fun l => hend l.2) (fun l => B l.2) (fun l => p l.2) (fun l => ε l.2) kF hk T hST

omit [Finite V.I₀] in
/-- The retained degree-one common-chart coframes determine all canonical
character powers over the same coefficient extension and on the same charts. -/
theorem commonMatchingCoframe_families
    (eNodes : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s)
    (heNodes : ∀ s x, eNodes s ((1 : K) ⊗ₜ[S] x) = (v.app s).hom x)
    (hqBase : q ≫ bsdhToSpec G (word ++ [i]) = cF.pt.hom)
    (T : Subalgebra ℤ K) (hST : S ≤ T)
    (hData : commonMatchingCoframeData G word i S N cN hcN deltaN hcoN hnN
      cF.pt.hom qN hK q
      (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN 1)
      V V₀ g a₀ c hend B p ε π jK T hST) :
    commonMatchingCoframeFamilyData G F cF hcF word i q point a ha beta hgroup hco hn
      S N v deltaN hd cN hcN qN hqN hcoN hnN hK V V₀ g a₀ c hend B p ε π jK T hST := by
  classical
  let W := matchingSingletonCover N cN hcN
  let C := appendCommonCover W V
  let : Finite W.I₀ := inferInstanceAs (Finite J)
  let : ∀ w, IsAffine (W.X w) := fun w =>
    inferInstanceAs (IsAffine (Spec (.of (N.obj (singletonIndex w)))))
  let : ∀ l, IsAffine (C.X l) := fun l => by
    let : IsAffine (W.X l.1) := inferInstance
    let : IsAffine (V.X l.2) := (inferInstance : ∀ z, IsAffine (V.X z)) l.2
    exact affine_fibre_product (W.f l.1) (V.f l.2)
  let : IsAffineHom qN := MorphismProperty.of_isPullback hK.flip inferInstance
  let P := fun l : C.I₀ => pullback (C.f l) qN
  let : ∀ l, IsAffine (P l) := fun l => inferInstance
  let M : C.I₀ → Type u := fun l => Γ(C.X l, ⊤)
  let A : C.I₀ → Type u := fun l => Γ(P l, ⊤)
  let : ∀ l, Algebra S (M l) := fun l =>
    ((C.f l ≫ cN.pt.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : ∀ l, Algebra K (A l) := fun l =>
    ((pullback.snd (C.f l) qN ≫ cF.pt.hom).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let j := fun l : C.I₀ => (C.X l).isoSpec.inv ≫ C.f l
  let jF := fun l : C.I₀ => (P l).isoSpec.inv ≫ pullback.snd (C.f l) qN
  obtain ⟨small, kN, kF, e, hscalar, hsmall, hk,
    hkn, hcross, hkf, he, hFlat, hFP, hStage⟩ := hData
  refine ⟨small, kN, kF, e, hscalar, hsmall, hk,
    hkn, hcross, hkf, he, hFlat, hFP, ?_⟩
  let : ∀ {s t : {s : Finset J // s.Nonempty}ᵒᵖ} (f : s ⟶ t),
      IsOpenImmersion (((N.op ⋙ algSpec (.of S)).map f).left) :=
    fun {_ _} f => inferInstanceAs
      (IsOpenImmersion (Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom)))
  let : (((N.op ⋙ algSpec (.of S)) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected := inferInstanceAs
    (((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected)
  have hlocal (z : J) := scalarColimit_isPullback N F v eNodes heNodes
    cN hcN cF hcF qN hqN (singletonIndex z)
  have hOver (l : C.I₀) := affineChart_over cF.pt.hom (pullback.snd (C.f l) qN)
  choose aOver haOver using hOver
  exact stage_family G F cF hcF word i q point a ha beta hgroup hco hn S N v deltaN hd
    cN hcN qN hqN hcoN hnN M A e j jF hscalar (fun l => l.1) small hsmall
    (fun l => V₀ l.2) (fun l => g l.2) (fun l => a₀ l.2) (fun l => c l.2)
    (fun l => hend l.2) (fun l => B l.2) (fun l => p l.2) (fun l => ε l.2) kF hk
    hqBase hlocal aOver haOver
    (fun l z => appendPolynomialChart_base G i (B l.2) (p l.2) (c l.2) z)
    T hST hStage

end Common

end SchubertGeometry.RetainedCharacter
