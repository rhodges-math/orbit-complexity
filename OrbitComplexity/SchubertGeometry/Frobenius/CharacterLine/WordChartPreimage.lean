import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordCharacterIdentification
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPolynomialChart
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-!
# Character coframes on inverse images of flag charts

The pullback of an opposition polynomial chart has a coframe for each power
of the matching line. The determinant section has the coefficient obtained
by pulling the opposition chart polynomial along the chart projection.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.RetainedCharacter
open scoped CategoryTheory.MonObj
open MonoidalCategory

namespace SchubertGeometry.RetainedCharacter

open private SchubertGeometry.CharacterLine.U
  SchubertGeometry.CharacterLine.pullSection
  SchubertGeometry.CharacterLine.pullSection_comp
  SchubertGeometry.CharacterLine.cancel_iso_frame
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.PullbackFrames

private def inducedFrame {X Y Z : Scheme.{u}} (k : X ⟶ Y) (q : Y ⟶ Z)
    (L : Y.Modules) (M : Z.Modules) (e : L ≅ (Scheme.Modules.pullback q).obj M)
    (E : (Scheme.Modules.pullback (k ≫ q)).obj M ≅ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback k).obj L ≅ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pullback k).mapIso e ≪≫ (pullbackComp k q).app M ≪≫ E


private theorem section_iso {X Y : Scheme.{u}} (k : X ⟶ Y)
    (L M : Y.Modules) (e : L ≅ M)
    (s : (𝟙_ Y.Modules) ⟶ L) (t : (𝟙_ Y.Modules) ⟶ M)
    (h : s ≫ e.hom = t) :
    SchubertGeometry.CharacterLine.pullSection k L s ≫ (Scheme.Modules.pullback k).map e.hom =
      SchubertGeometry.CharacterLine.pullSection k M t := by
  dsimp only [SchubertGeometry.CharacterLine.pullSection]
  rw [Category.assoc, ← Functor.map_comp, h]


private theorem compose_chain {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : A ⟶ D)
    (v r : A ⟶ E) (hab : a ≫ b = d) (hd : d ≫ c = v) (hv : v = r) :
    a ≫ b ≫ c = r := by
  calc
    a ≫ b ≫ c = (a ≫ b) ≫ c := (Category.assoc a b c).symm
    _ = d ≫ c := congrArg (fun f => f ≫ c) hab
    _ = v := hd
    _ = r := hv

private theorem left_associate {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (t : A ⟶ E)
    (h : a ≫ b ≫ c = t) : (a ≫ b) ≫ c = t :=
  (Category.assoc a b c).trans h

private theorem inducedFrame_section {X Y Z : Scheme.{u}}
    (k : X ⟶ Y) (q : Y ⟶ Z) (L : Y.Modules) (M : Z.Modules)
    (e : L ≅ (Scheme.Modules.pullback q).obj M)
    (E : (Scheme.Modules.pullback (k ≫ q)).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (s : (𝟙_ Y.Modules) ⟶ L) (t : SheafOfModules.unit Z.ringCatSheaf ⟶ M)
    (h : s ≫ e.hom = SchubertGeometry.CharacterLine.pullSection q M t) (r : Γ(X, ⊤))
    (hE : SchubertGeometry.CharacterLine.pullSection (k ≫ q) M t ≫ E.hom =
      globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r) :
    SchubertGeometry.CharacterLine.pullSection k L s ≫ (inducedFrame k q L M e E).hom =
      globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r := by
  change SchubertGeometry.CharacterLine.pullSection k L s ≫
    ((Scheme.Modules.pullback k).map e.hom ≫ ((pullbackComp k q).hom.app M ≫ E.hom)) = _
  exact compose_chain (SchubertGeometry.CharacterLine.pullSection k L s)
    ((Scheme.Modules.pullback k).map e.hom)
    ((pullbackComp k q).hom.app M ≫ E.hom)
    (SchubertGeometry.CharacterLine.pullSection k ((Scheme.Modules.pullback q).obj M)
      (SchubertGeometry.CharacterLine.pullSection q M t))
    (SchubertGeometry.CharacterLine.pullSection (k ≫ q) M t ≫ E.hom)
    (globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r)
    (section_iso k L ((Scheme.Modules.pullback q).obj M) e s
      (SchubertGeometry.CharacterLine.pullSection q M t) h)
    (SchubertGeometry.CharacterLine.cancel_iso_frame ((pullbackComp k q).app M)
      (SchubertGeometry.CharacterLine.pullSection_comp k q M t) E.hom) hE

private theorem framedSection_value {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (E : (Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (r t : Γ(X, ⊤))
    (hs : (pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s ≫ E.hom =
      globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r)
    (hr : r = t) :
    SchubertGeometry.CharacterLine.pullSection f M s ≫ E.hom =
      globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) t := by
  have h := left_associate (pullbackObjUnitIso f).inv
    ((Scheme.Modules.pullback f).map s) E.hom
    (globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r) hs
  exact h.trans (congrArg
    (globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf)) hr)


private theorem pulled_coefficient {P A U V : Scheme.{u}}
    (p : P ⟶ A) (b : A ⟶ U) (j : U ⟶ V)
    (s : Γ(V, ⊤)) (r : Γ(A, ⊤)) (h : (b ≫ j).appTop s = r) :
    ((p ≫ b) ≫ j).appTop s = p.appTop r := by
  rw [Category.assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h]

private theorem over_appTop_value {S : Scheme.{u}} {A B C : Over S}
    (f : A ⟶ B) (g : B ⟶ C) (b : A.left ⟶ B.left) (hb : b = f.left)
    (s : Γ(C.left, ⊤)) (r : Γ(A.left, ⊤)) (h : (f ≫ g).left.appTop s = r) :
    (b ≫ g.left).appTop s = r := by
  subst b
  exact h



private def schemeTarget {k : Type u} [Field k] (V : GroupActions.Variety k)
    {X : Scheme.{u}} (a : X ⟶ V.toOver.left) : X ⟶ V.scheme := a

private def schemeSource {k : Type u} [Field k] (V : GroupActions.Variety k)
    {X : Scheme.{u}} (a : V.toOver.left ⟶ X) : V.scheme ⟶ X := a

private theorem schemeTarget_comp {k : Type u} [Field k] (V : GroupActions.Variety k)
    {X Y : Scheme.{u}} (a : X ⟶ V.toOver.left) (b : V.toOver.left ⟶ Y)
    (f : X ⟶ Y) (h : a ≫ b = f) :
    schemeTarget V a ≫ schemeSource V b = f := h

private theorem schemeTarget_value {k : Type u} [Field k] (V : GroupActions.Variety k)
    {X Y : Scheme.{u}} (a : X ⟶ V.toOver.left) (b : V.toOver.left ⟶ Y)
    (s : Γ(Y, ⊤)) (r : Γ(X, ⊤)) (h : (a ≫ b).appTop s = r) :
    (schemeTarget V a ≫ schemeSource V b).appTop s = r := h


variable {K : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K)

private def polynomialSection (i : G.rootBase.support) (n : ℕ) :=
  DeterminantSection.affineSection (K := K) (Polynomial (G.rootSubsetAlgebra
        {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i)}
        (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i))))
    (DeterminantSection.oppositionChartPolynomial G i n)

/-- The inverse image of an opposition polynomial flag chart under the word map. -/
def wordChartPreimage {X : Scheme.{u}} (word : List G.rootBase.support)
    (q : X ⟶ bsdhScheme G word) (i : G.rootBase.support) : Scheme.{u} :=
  CategoryTheory.Limits.pullback (DeterminantSection.oppositionPolynomialMap G i).left
    (q ≫ bsdhMap G word)

private def preimageSnd {X : Scheme.{u}} (word : List G.rootBase.support)
    (q : X ⟶ bsdhScheme G word) (i : G.rootBase.support) :
    wordChartPreimage G word q i ⟶ X :=
  pullback.snd (DeterminantSection.oppositionPolynomialMap G i).left (q ≫ bsdhMap G word)

private def preimageFst {X : Scheme.{u}} (word : List G.rootBase.support)
    (q : X ⟶ bsdhScheme G word) (i : G.rootBase.support) :
    wordChartPreimage G word q i ⟶
      (affineVariety K
        (Polynomial (G.rootSubsetAlgebra
        {r | G.rootBase.IsPos r ∧ r ∉ leftRootInversionIndices G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i)}
        (PositiveRootClosedSets.isPositiveRootClosed G.rootBase
          (RootPairing.weylGroup.ofIdx G.rootSystem i))))).toOver.left :=
  pullback.fst (DeterminantSection.oppositionPolynomialMap G i).left (q ≫ bsdhMap G word)

private theorem preimage_equation {X : Scheme.{u}} (word : List G.rootBase.support)
    (q : X ⟶ bsdhScheme G word) (i : G.rootBase.support) :
    preimageFst G word q i ≫ (DeterminantSection.oppositionPolynomialMap G i).left =
      (preimageSnd G word q i ≫ q) ≫ bsdhMap G word :=
  (pullback.condition (f := (DeterminantSection.oppositionPolynomialMap G i).left)
    (g := q ≫ bsdhMap G word)).trans
      (Category.assoc (preimageSnd G word q i) q (bsdhMap G word)).symm


private def preimageLift {X : Scheme.{u}} (word : List G.rootBase.support)
    (q : X ⟶ bsdhScheme G word) (i : G.rootBase.support) :
    wordChartPreimage G word q i ⟶ SchubertGeometry.CharacterLine.U G :=
  schemeTarget (oppositeUnipotentVariety G)
    (preimageFst G word q i ≫ (DeterminantSection.oppositionPolynomialIso G i).hom.left)

private theorem preimageLift_equation {X : Scheme.{u}} (word : List G.rootBase.support)
    (q : X ⟶ bsdhScheme G word) (i : G.rootBase.support) :
    preimageLift G word q i ≫
      schemeSource (oppositeUnipotentVariety G)
        (flagChartMorphism G (DeterminantSection.oppositionChartPoint G i)).left =
      (preimageSnd G word q i ≫ q) ≫ bsdhMap G word :=
  schemeTarget_comp (oppositeUnipotentVariety G)
    (preimageFst G word q i ≫ (DeterminantSection.oppositionPolynomialIso G i).hom.left)
    (flagChartMorphism G (DeterminantSection.oppositionChartPoint G i)).left
    ((preimageSnd G word q i ≫ q) ≫ bsdhMap G word)
    ((Category.assoc (preimageFst G word q i)
      (DeterminantSection.oppositionPolynomialIso G i).hom.left
      (flagChartMorphism G (DeterminantSection.oppositionChartPoint G i)).left).trans
        (preimage_equation G word q i))


private theorem unipotentTarget_value {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) (V : GroupActions.Variety K) {X : Scheme.{u}}
    (a : X ⟶ (oppositeUnipotentVariety G).toOver.left)
    (aU : X ⟶ SchubertGeometry.CharacterLine.U G)
    (ha : aU = schemeTarget (oppositeUnipotentVariety G) a)
    (b : (oppositeUnipotentVariety G).toOver.left ⟶ V.toOver.left)
    (s : Γ(V.scheme, ⊤)) (r : Γ(X, ⊤)) (h : (a ≫ b).appTop s = r) :
    (aU ≫ b).appTop s = r := by
  subst aU
  simpa only [SchubertGeometry.CharacterLine.U, schemeSource] using
    schemeTarget_value (oppositeUnipotentVariety G) a b s r h

private theorem preimageFrame_value {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K) {Y : Scheme.{u}}
    (word : List G.rootBase.support) (q : Y ⟶ bsdhScheme G word)
    (i : G.rootBase.support) (n : ℕ)
    (r : Γ(wordChartPreimage G word q i, ⊤))
    (hcoeff : (((preimageFst G word q i ≫
      (DeterminantSection.oppositionPolynomialIso G i).hom.left) ≫
      (flagChartMap G (DeterminantSection.oppositionChartPoint G i)).left).appTop
        (DeterminantSection.positiveDetPowerFunction G n)) = r) :
    SchubertGeometry.CharacterLine.pullSection (preimageSnd G word q i ≫ q)
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word)
      (CharacterLine.wordDeterminantModuleSection G n word) ≫
      (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ n)
        (preimageSnd G word q i ≫ q) (DeterminantSection.oppositionChartPoint G i)
        (preimageLift G word q i) (preimageLift_equation G word q i)).hom =
      globalSectionsSmul (SheafOfModules.unit (wordChartPreimage G word q i).ringCatSheaf) r := by
  have valueSeed := @unipotentTarget_value.{u} K hK hAlg hChar G (reductiveVariety G)
    (wordChartPreimage G word q i)
  have valueA := valueSeed
    (preimageFst G word q i ≫ (DeterminantSection.oppositionPolynomialIso G i).hom.left)
  have valueU := valueA (preimageLift G word q i)
  have hlift : preimageLift G word q i =
      schemeTarget (oppositeUnipotentVariety G)
        (preimageFst G word q i ≫ (DeterminantSection.oppositionPolynomialIso G i).hom.left) := rfl
  have valueLift := valueU hlift
  have valueMaps := valueLift (flagChartMap G (DeterminantSection.oppositionChartPoint G i)).left
  have valueS := valueMaps (DeterminantSection.positiveDetPowerFunction G n)
  have valueR := valueS r
  have hvLift := valueR hcoeff
  have hframe :=
    @CharacterLine.wordDeterminantModule_frame.{u} K hK hAlg hChar G n word
    (wordChartPreimage G word q i) (preimageSnd G word q i ≫ q)
    (DeterminantSection.oppositionChartPoint G i) (preimageLift G word q i)
    (preimageLift_equation G word q i)
  have hcarrier := @framedSection_value (wordChartPreimage G word q i) (bsdhScheme G word)
    (preimageSnd G word q i ≫ q)
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word)
    (CharacterLine.wordDeterminantModuleSection G n word)
    (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ n)
      (preimageSnd G word q i ≫ q) (DeterminantSection.oppositionChartPoint G i)
      (preimageLift G word q i) (preimageLift_equation G word q i))
    ((preimageLift G word q i ≫ (flagChartMap G
      (DeterminantSection.oppositionChartPoint G i)).left).appTop
        (DeterminantSection.positiveDetPowerFunction G n)) r
  have hframed := hcarrier hframe
  have hvalue := hframed hvLift
  exact hvalue

open private singletonIndex
  from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift
  from OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase

variable {J : Type u}
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
    {R : Type u} [hR : CommRing R]
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

/-- The character coframe of the matching line on the entire flag-chart inverse image. -/
def wordChartPreimageFrame (i : G.rootBase.support) (n : ℕ) :
    (Scheme.Modules.pullback (preimageSnd G word q i)).obj
        ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n)) ≅
      SheafOfModules.unit (wordChartPreimage G word q i).ringCatSheaf :=
  inducedFrame (preimageSnd G word q i) q
    ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n))
    (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ n) word)
    (@retainedWordLineIso K hK hAlg hChar G J F hFopen hFdir cF hcF word q
      point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN
      hcoN hnN n)
    (CharacterLine.wordCharacterFrameIso G word (G.positiveRootCharacter ^ n)
      (preimageSnd G word q i ≫ q)
      (DeterminantSection.oppositionChartPoint G i)
      (preimageLift G word q i)
      (preimageLift_equation G word q i))


end SchubertGeometry.RetainedCharacter
