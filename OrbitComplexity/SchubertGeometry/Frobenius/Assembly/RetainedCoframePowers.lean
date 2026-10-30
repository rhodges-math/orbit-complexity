import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedCoframePowers
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCharacterIdentification
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!+# Powers of retained character coframe quotients

The canonical scalar comparison of matching modules transports both coframes
on a common chart. Their quotient is unchanged, so the degree-one quotient
determines every character power on the same retained model.
-/

noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits (Cocone IsColimit)
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace SchubertGeometry.RetainedCharacter

open private comparisonCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendCoframeComparison
open private unit_ratio_from_scalar from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendPowerFrames
open private polynomialBase from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.AppendCoordinates
open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits

private theorem coframeUnit_precompose (A : Type u) [CommRing A]
    {L M : (Spec (.of A)).Modules} (T : L ≅ M)
    (E F : M ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf) :
    affineCoframeUnit A (T ≪≫ E) (T ≪≫ F) = affineCoframeUnit A E F := by
  apply unit_ratio_from_scalar A (T ≪≫ E) (T ≪≫ F) (affineCoframeUnit A E F)
  have h := affineCoframeUnit_hom A E F
  change F.hom = E.hom ≫ Scheme.Modules.globalSectionsSmul
    (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    ((Scheme.ΓSpecIso (.of A)).inv (affineCoframeUnit A E F : A)) at h
  change T.hom ≫ F.hom = (T.hom ≫ E.hom) ≫ Scheme.Modules.globalSectionsSmul
    (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    ((Scheme.ΓSpecIso (.of A)).inv (affineCoframeUnit A E F : A))
  exact (congrArg (fun g => T.hom ≫ g) h).trans
    (Category.assoc T.hom E.hom (Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
      ((Scheme.ΓSpecIso (.of A)).inv (affineCoframeUnit A E F : A)))).symm

private theorem coframeUnit_transport (A : Type u) [CommRing A]
    {L M : (Spec (.of A)).Modules} (T : L ≅ M)
    (E F : M ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    (E' F' : L ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    (hE : E' = T ≪≫ E) (hF : F' = T ≪≫ F) :
    affineCoframeUnit A E' F' = affineCoframeUnit A E F := by
  subst E'
  subst F'
  exact coframeUnit_precompose A T E F

private theorem comparisonCoframe_change {P X Y Q : Scheme.{u}}
    (j : P ⟶ X) (q : X ⟶ Y) (k : P ⟶ Q) (r : Q ⟶ Y)
    (h : j ≫ q = k ≫ r) (M M' : X.Modules) (N : Y.Modules)
    (T : M ≅ M') (E : M ≅ (pullback q).obj N)
    (E' : M' ≅ (pullback q).obj N) (hE : E = T ≪≫ E')
    (e : (pullback r).obj N ≅ SheafOfModules.unit Q.ringCatSheaf) :
    comparisonCoframe j q k r h M N E e =
      (pullback j).mapIso T ≪≫ comparisonCoframe j q k r h M' N E' e := by
  subst E
  apply Iso.ext
  simp only [comparisonCoframe, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) {J : Type u}
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
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

/-- The canonical scalar matching comparison preserves the power law for
the quotient of matching and polynomial append coframes on each common chart. -/
theorem retainedCoframe_unit_power
    (A : CommAlgCat.{u} K) (s : {s : Finset J // s.Nonempty}) (j : J) (hj : j ∈ s.val)
    (f : (algSpec (.of K)).obj (op A) ⟶ (algSpec (.of K)).obj (op (F.obj s)))
    (V : Over (Spec (.of K))) (g : G.points)
    (b : V ⟶ (oppositeUnipotentVariety G).toOver)
    (c : V ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : c.left ≫ (bsdhAppendIso G word i).hom.left ≫
      CategoryTheory.Limits.pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (b ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
          flagBundleChart G _ g)
    (B : CommAlgCat.{u} K) (p : (algSpec (.of K)).obj (op B) ⟶ V) (ε : Fin 2)
    (k : (algSpec (.of K)).obj (op A) ⟶ polynomialBase B)
    (h : (f.left ≫ (cF.ι.app (op s)).left) ≫ q = k.left ≫
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c)) :
    let T := fun n : ℕ => matchingPullbackIso N F cN hcN cF hcF v qN hqN
      deltaN (wordTransitionUnit G F beta) hd n hcoN hnN hco hn
    let E := fun n : ℕ => (pullback (f.left ≫ (cF.ι.app (op s)).left)).mapIso (T n) ≪≫
      frame_on_composite f.left (cF.ι.app (op s)).left
        (f.left ≫ (cF.ι.app (op s)).left) rfl
        (matchingModule F cF (wordTransitionUnit G F beta) n)
        (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta)
          n hco hn s j hj)
    let H := fun n : ℕ => comparisonCoframe (f.left ≫ (cF.ι.app (op s)).left) q k.left
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c) h
      ((pullback qN).obj (matchingModule N cN deltaN n))
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) (word ++ [i]))
      (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN n)
      (appendPolynomialFrame G word i V g b c hend B p n ⟨ε⟩)
    ∀ n : ℕ, affineCoframeUnit A (E n) (H n) = (affineCoframeUnit A (E 1) (H 1)) ^ n := by
  intro T E H n
  let E₀ := fun r : ℕ => frame_on_composite f.left (cF.ι.app (op s)).left
    (f.left ≫ (cF.ι.app (op s)).left) rfl
    (matchingModule F cF (wordTransitionUnit G F beta) r)
    (localCharacterTrivialization F cF hcF (wordTransitionUnit G F beta)
      r hco hn s j hj)
  let H₀ := fun r : ℕ => comparisonCoframe (f.left ≫ (cF.ι.app (op s)).left) q k.left
    (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c) h
    (matchingModule F cF (wordTransitionUnit G F beta) r)
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ r) (word ++ [i]))
    (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q r
      point a ha beta hgroup hco hn).symm
    (appendPolynomialFrame G word i V g b c hend B p r ⟨ε⟩)
  have hH (r : ℕ) : H r =
      (pullback (f.left ≫ (cF.ι.app (op s)).left)).mapIso (T r) ≪≫ H₀ r :=
    comparisonCoframe_change (f.left ≫ (cF.ι.app (op s)).left) q k.left
      (projectiveLinePolynomialChart B ⟨ε⟩ ≫ projectiveAppendChart G i B p c) h
      ((pullback qN).obj (matchingModule N cN deltaN r))
      (matchingModule F cF (wordTransitionUnit G F beta) r)
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ r) (word ++ [i]))
      (T r)
      (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN r)
      (wordCharacterMatchingIso G F cF hcF (word ++ [i]) q r
        point a ha beta hgroup hco hn).symm rfl
      (appendPolynomialFrame G word i V g b c hend B p r ⟨ε⟩)
  have hu (r : ℕ) : affineCoframeUnit A (E r) (H r) = affineCoframeUnit A (E₀ r) (H₀ r) :=
    coframeUnit_transport A
      ((pullback (f.left ≫ (cF.ι.app (op s)).left)).mapIso (T r))
      (E₀ r) (H₀ r) (E r) (H r) rfl (hH r)
  have hp := refinedCoframe_unit_power G F cF hcF word i q point a ha beta hgroup hco hn
    A s j hj f V g b c hend B p ε k h
  calc
    affineCoframeUnit A (E n) (H n) = affineCoframeUnit A (E₀ n) (H₀ n) := hu n
    _ = (affineCoframeUnit A (E₀ 1) (H₀ 1)) ^ n := hp n
    _ = (affineCoframeUnit A (E 1) (H 1)) ^ n :=
      congrArg (fun d : Aˣ => d ^ n) (hu 1).symm

end SchubertGeometry.RetainedCharacter
