import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingRetention
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Borel chart data in the append coefficient models

Polynomial chart comparisons retain their source, base, and word-line maps
while the coefficient ring is extended.
-/

set_option autoImplicit false
set_option pp.maxSteps 1000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open FrobeniusSplitting FrobeniusSplitting.RetainedCharacter ReductiveGroups
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace SchubertGeometry

open RetainedCharacter

universe u

open private initialCoefficient finalCoefficient polynomialSpecMap
  cancel_chart_iso cancel_chart_pair cancel_chart_base join_chart_squares join_chart_base
  scalar_field_chart_equation from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendScalarComparisons
open private matchingCommonField from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingStageGeometry
open private chartThroughIso from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingRetention
open private borelPolynomialLeg from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendBorelCharts
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private singletonIndex singletonArrow from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private coordinateScalarBase coordinateScalarMap fieldCoordinateCocone
  fieldCoordinateCocone_colimit fieldCoordinateDiagram_opens fieldCoordinateMap
  inverseCoordinates_affine retainedCoordinateRings singleCoordinateRings
  from OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordModelSection
open private inverseOpenDiagram
  from OrbitComplexity.SchubertGeometry.Normality.Transitions.PriorCoconeComparison
open private map_exists_witness map_and_tail from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendWordModel

private def appendChartTriangle {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (i : G.rootBase.support) {I : Type u}
    (V₀ : I → Over (Spec (.of K)))
    (c : ∀ j, V₀ j ⊗
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (g : I → G.points)
    (a₀ : ∀ j, V₀ j ⟶ (oppositeUnipotentVariety G).toOver) : Prop :=
  ∀ j, (c j).left ≫ (bsdhAppendIso G word i).hom.left ≫
    pullback.snd (bsdhMap G word) (flagBundleProjection G
      (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
    (a₀ j ⊗ₘ 𝟙 (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫
        flagBundleChart G _ (g j)

section ChartRings

variable {A₀ A₁ A₂ : Type u} [CommRing A₀] [CommRing A₁] [CommRing A₂]
    [Algebra A₀ A₁] [Algebra A₁ A₂]
    {I : Type u} (A : I → CommAlgCat.{u} A₀)
    {Y Z X : Scheme.{u}}

private def firstCoefficient (B : CommAlgCat.{u} A₀) : CommAlgCat.{u} A₁ :=
  .of A₁ (A₁ ⊗[A₀] B)

private def firstChartIsos (V : Y.OpenCover.{u}) (index : V.I₀ → I) : Type _ :=
  ∀ j, V.X j ≅ Spec (.of (Polynomial (A₁ ⊗[A₀] A (index j))))

private def firstChartSquare (V : Y.OpenCover.{u}) (index : V.I₀ → I)
    (E : firstChartIsos (A₁ := A₁) A V index) (q : Y ⟶ X)
    (leg : ∀ j, Spec (.of (Polynomial (A (index j)))) ⟶ X) : Prop :=
  ∀ j, V.f j ≫ q = (E j).hom ≫
    polynomialSpecMap (Algebra.TensorProduct.includeRight :
      A (index j) →ₐ[A₀] A₁ ⊗[A₀] A (index j)).toRingHom ≫ leg j

private def firstChartBase (V : Y.OpenCover.{u}) (index : V.I₀ → I)
    (E : firstChartIsos (A₁ := A₁) A V index) (base : Y ⟶ Spec (.of A₁)) : Prop :=
  ∀ j, V.f j ≫ base = (E j).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap A₁ (Polynomial (A₁ ⊗[A₀] A (index j)))))

private def scalarChartIsos (V : Z.OpenCover.{u}) (index : V.I₀ → I) : Type _ :=
  ∀ j, V.X j ≅ Spec (.of (Polynomial (A₂ ⊗[A₁] (A₁ ⊗[A₀] A (index j)))))

private def scalarChartSquare (W : Y.OpenCover.{u}) (V : Z.OpenCover.{u})
    (firstIndex : W.I₀ → I) (index : V.I₀ → W.I₀)
    (E₀ : firstChartIsos (A₁ := A₁) A W firstIndex)
    (E : scalarChartIsos (A₁ := A₁) (A₂ := A₂) A V (fun j => firstIndex (index j)))
    (q : Z ⟶ Y) : Prop :=
  ∀ j, V.f j ≫ q = (E j).hom ≫
    polynomialSpecMap (Algebra.TensorProduct.includeRight :
      A₁ ⊗[A₀] A (firstIndex (index j)) →ₐ[A₁]
        A₂ ⊗[A₁] (A₁ ⊗[A₀] A (firstIndex (index j)))).toRingHom ≫
          (E₀ (index j)).inv ≫ W.f (index j)

private def scalarChartBase (V : Z.OpenCover.{u}) (index : V.I₀ → I)
    (E : scalarChartIsos (A₁ := A₁) (A₂ := A₂) A V index)
    (base : Z ⟶ Spec (.of A₂)) : Prop :=
  ∀ j, V.f j ≫ base = (E j).hom ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap A₂ (Polynomial (A₂ ⊗[A₁] (A₁ ⊗[A₀] A (index j))))))

end ChartRings

private structure AppendChartData {K : Type u}
    [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) (i : G.rootBase.support) where
  I : Type u
  F : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} K
  N : {s : Finset I // s.Nonempty} ⥤ CommAlgCat.{u} S
  e : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s
  sel : ∀ s : {s : Finset I // s.Nonempty}, {j // j ∈ s.val}
  V₀ : I → Over (Spec (.of K))
  p : ∀ (s : {s : Finset I // s.Nonempty}) (j : I) (_ : j ∈ s.val),
    (algSpec (.of K)).obj (op (F.obj s)) ⟶ V₀ j
  c : ∀ j, V₀ j ⊗
    (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
      Over.mk (bsdhToSpec G (word ++ [i]))
  g : I → G.points
  a₀ : ∀ j, V₀ j ⟶ (oppositeUnipotentVariety G).toOver
  hend : @appendChartTriangle.{u} K kField kClosed kZero G word i I V₀ c g a₀
  b : ∀ s, Spec (.of (F.obj s)) ⟶ bsdhScheme G word
  hbbase : ∀ s, b s ≫ bsdhToSpec G word =
    Spec.map (CommRingCat.ofHom (algebraMap K (F.obj s)))

private structure AppendChartContext {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    {S : Subalgebra ℤ K} {G : ReductiveGroupData K}
    {word : List G.rootBase.support} {i : G.rootBase.support}
    (input : AppendChartData S G word i) where
  D : {s : Finset input.I // s.Nonempty}ᵒᵖ ⥤ Scheme.{u}
  eP : ∀ s, D.obj (op s) ≅ projectiveScheme (input.N.obj s) (ULift.{u} (Fin 2))
  cD : Cocone D
  hOpen : ∀ s, IsOpenImmersion (cD.ι.app s)
  hCover : ∀ (Z : Scheme.{u}) (f : Z ⟶ cD.pt) (z : Z),
    ∃ s, ∃ x : (pullback f (cD.ι.app s) : Scheme.{u}),
      pullback.fst f (cD.ι.app s) x = z
  base : cD.pt ⟶ Spec (.of S)
  m : bsdhScheme G (word ++ [i]) ⟶ cD.pt
  hCart : IsPullback m (bsdhToSpec G (word ++ [i])) base
    (Spec.map (CommRingCat.ofHom (algebraMap S K)))
  hfield : ∀ s j, borelPolynomialLeg G word i input.F input.sel input.V₀ input.p input.c s j ≫ m =
    polynomialSpecMap (initialCoefficient (input.e s)) ≫
      (projectiveLinePolynomialChart (input.N.obj s) j ≫ (eP s).inv ≫ cD.ι.app (op s))
  hprior : ∀ s j, borelPolynomialLeg G word i input.F input.sel input.V₀ input.p input.c s j ≫
    bsdhAppendFst G word i =
      Spec.map (CommRingCat.ofHom
        (Polynomial.C : input.F.obj s →+* Polynomial (input.F.obj s))) ≫ input.b s

private structure AppendChartStage {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    {S₀ : Subalgebra ℤ K} {G : ReductiveGroupData K}
    {word : List G.rootBase.support} {i : G.rootBase.support}
    (S : Subalgebra ℤ K) (hS₀ : S₀ ≤ S)
    {input : AppendChartData S₀ G word i} (old : AppendChartContext input)
    {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    (m : bsdhScheme G (word ++ [i]) ⟶ Y) where
  q : Y ⟶ old.cD.pt
  hm : m ≫ q = old.m
  V : Y.OpenCover.{u}
  finite : Finite V.I₀
  affine : ∀ j, IsAffine (V.X j)
  index : V.I₀ ≃ (appendPolynomialCover input.N old.D old.eP old.cD
    old.hOpen old.hCover).I₀
  eV :
    let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
    firstChartIsos (A₁ := S) input.N.obj V (fun j => (index j).1)
  hold :
    let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
    firstChartSquare (A₁ := S) input.N.obj V (fun j => (index j).1) eV q
      (fun j => (appendPolynomialCover input.N old.D old.eP old.cD
        old.hOpen old.hCover).f (index j))
  hbase :
    let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
    firstChartBase (A₁ := S) input.N.obj V (fun j => (index j).1) eV base


private def contextChartIsos {K : Type u}
    [Field K] [IsAlgClosed K] [CharZero K]
    (S R : Subalgebra ℤ K) (hSR : S ≤ R)
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    {S₀ : Subalgebra ℤ K} (hS₀ : S₀ ≤ S)
    (input : AppendChartData S₀ G word i) (old : AppendChartContext input)
    {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    (m : bsdhScheme G (word ++ [i]) ⟶ Y)
    (d : AppendChartStage S hS₀ old base m)
    {Z : Scheme.{u}} (V : Z.OpenCover.{u}) (index : V.I₀ ≃ d.V.I₀) : Type _ :=
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
  scalarChartIsos (A₁ := S) (A₂ := R) input.N.obj V
    (fun j => (d.index (index j)).1)



section FlatContext

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    {S₀ : Subalgebra ℤ K} (input : AppendChartData S₀ G word i)
    (old : AppendChartContext input) (R : Subalgebra ℤ K) (hS₀R : S₀ ≤ R)
    {J : Type u} (jFinite : Finite J)
    (MN : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (MN.map f).hom.toRingHom)))
    (hNdir : ((MN.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected)
    (cN : Cocone (MN.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    (hSep : cN.pt.left.IsSeparated)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (MN.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hnat : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (MN.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    {Z : Scheme.{u}} (baseK : Z ⟶ Spec (.of K))
    (n : Z ⟶ cN.pt.left) (r : Z ⟶ bsdhScheme G (word ++ [i]))
    (hK : IsPullback n baseK cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (EL : (Scheme.Modules.pullback n).obj (matchingModule MN cN delta 1) ≅
      (Scheme.Modules.pullback r).obj
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) (word ++ [i])))
    (nWord : bsdhScheme G (word ++ [i]) ⟶ cN.pt.left)
    (dR : @AppendChartStage.{u} K kField kClosed kZero S₀ G word i R hS₀R
      input old cN.pt.left cN.pt.hom nWord)

private def contextRetentionData (Q : Subalgebra ℤ K) (hRQ : R ≤ Q) : Prop :=
  let : Algebra S₀ R := (Subalgebra.inclusion hS₀R).toAlgebra
  ∃ (πField : ∀ z, Spec (.of (Polynomial (input.F.obj (dR.index z).1))) ⟶ dR.V.X z)
    (jK : ∀ z, Spec (.of (Polynomial (input.F.obj (dR.index z).1))) ⟶ Z),
    (∀ z, IsPullback (πField z) (jK z) (dR.V.f z) n) ∧
    (∀ z, jK z ≫ r = @borelPolynomialLeg.{u} K input.I kField kClosed kZero
      G word i input.F input.sel input.V₀ input.p input.c (dR.index z).1 (dR.index z).2) ∧
    (∀ z, πField z = polynomialSpecMap
      (initialCoefficient (S := R)
        (@scalarDiagramComparison.{u,u,u} K kField S₀ R hS₀R
          {s : Finset input.I // s.Nonempty}
          (inferInstanceAs (Category.{u} {s : Finset input.I // s.Nonempty}))
          input.N input.F input.e (dR.index z).1)) ≫ (dR.eV z).inv) ∧
    (∀ z, jK z ≫ baseK = Spec.map (CommRingCat.ofHom
      (algebraMap K (Polynomial (input.F.obj (dR.index z).1))))) ∧
    @commonMatchingCoframeData.{u} K kField kClosed kZero G word i R J jFinite MN
      (@hNopen) hNdir cN hcN hSep delta hco hnat Z baseK n hK r EL dR.V dR.affine
      (fun z => input.V₀ (input.sel (dR.index z).1).val)
      (fun z => input.g (input.sel (dR.index z).1).val)
      (fun z => input.a₀ (input.sel (dR.index z).1).val)
      (fun z => input.c (input.sel (dR.index z).1).val)
      (fun z => input.hend (input.sel (dR.index z).1).val)
      (fun z => input.F.obj (dR.index z).1)
      (fun z => input.p (dR.index z).1
        (input.sel (dR.index z).1).val (input.sel (dR.index z).1).property)
      (fun z => (dR.index z).2) πField jK Q hRQ

end FlatContext

section Context

variable {K : Type u} [kField : Field K] [kClosed : IsAlgClosed K] [kZero : CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) {S₀ : Subalgebra ℤ K} (hS₀ : S₀ ≤ S)
    (input : AppendChartData S₀ G word i) (old : AppendChartContext input)
    {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    (m : bsdhScheme G (word ++ [i]) ⟶ Y)
    (d : AppendChartStage S hS₀ old base m)
    (R : Subalgebra ℤ K) (hSR : S ≤ R)
    {J : Type u} [jFinite : Finite J]
    (MN : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (MN.map f).hom.toRingHom))]
    [hNdir : ((MN.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (MN.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
    [hSep : cN.pt.left.IsSeparated] [hSmooth : Smooth cN.pt.hom]
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (MN.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hnat : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (MN.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    {Z : Scheme.{u}} (baseK : Z ⟶ Spec (.of K))
    (n : Z ⟶ cN.pt.left) (r : Z ⟶ bsdhScheme G (word ++ [i]))
    (hK : IsPullback n baseK cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (EL : (Scheme.Modules.pullback n).obj (matchingModule MN cN delta 1) ≅
      (Scheme.Modules.pullback r).obj
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) (word ++ [i])))
    (E : Z ≅ bsdhScheme G (word ++ [i]))
    (V : cN.pt.left.OpenCover.{u}) [vFinite : Finite V.I₀] [vAffine : ∀ v, IsAffine (V.X v)]
    (index : V.I₀ ≃ d.V.I₀)
    (eV : contextChartIsos S R hSR G word i hS₀ input old base m d V index)

private theorem retain_chart_context (q : cN.pt.left ⟶ Y)
    (nWord : bsdhScheme G (word ++ [i]) ⟶ cN.pt.left)
    (hWord : E.hom ≫ nWord = n)
    (hdS : IsPullback d.q base old.base
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀).toRingHom)))
    (hq : IsPullback q cN.pt.hom base
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hSR).toRingHom)))
    (hE : E.hom ≫ bsdhToSpec G (word ++ [i]) = baseK) (hEr : E.hom = r)
    (hn : n ≫ q = E.hom ≫ m)
    (hV :
      let _sRAlg : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let _s0SAlg : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
      scalarChartSquare (A₁ := S) (A₂ := R) input.N.obj d.V V
        (fun j => (d.index j).1) index d.eV eV q)
    (hVbase :
      let _sRAlg : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let _s0SAlg : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
      scalarChartBase (A₁ := S) (A₂ := R) input.N.obj V
        (fun j => (d.index (index j)).1) eV cN.pt.hom)
    (hR : R.FG)
    (hWaff : ∀ j, IsAffine ((matchingSingletonCover MN cN hcN).X j))
    (hCsm : ∀ l, Smooth
      ((appendCommonCover (matchingSingletonCover MN cN hcN) V).f l ≫ cN.pt.hom))
    (hCommon :
      let : ∀ j, IsAffine ((matchingSingletonCover MN cN hcN).X j) := hWaff
      matchingCommonField Subtype.val_injective cN.pt.hom baseK n hK
        (matchingSingletonCover MN cN hcN) V) :
    let : ∀ j, IsAffine ((matchingSingletonCover MN cN hcN).X j) := hWaff
    ∃ dR : @AppendChartStage.{u} K kField kClosed kZero S₀ G word i R
        (hS₀.trans hSR) input old cN.pt.left cN.pt.hom nWord,
      let : ∀ z, IsAffine (dR.V.X z) := dR.affine
      IsPullback dR.q cN.pt.hom old.base
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hS₀.trans hSR)).toRingHom)) ∧
      (∀ l, Smooth ((appendCommonCover (matchingSingletonCover MN cN hcN) dR.V).f l ≫
        cN.pt.hom)) ∧
      matchingCommonField Subtype.val_injective cN.pt.hom baseK n hK
        (matchingSingletonCover MN cN hcN) dR.V ∧
      ∃ (Q : Subalgebra ℤ K) (hRQ : R ≤ Q), Q.FG ∧
        @contextRetentionData.{u} K kField kClosed kZero G word i S₀ input old R
          (hS₀.trans hSR) J jFinite MN (@hNopen) hNdir cN hcN hSep delta hco hnat
          Z baseK n r hK EL nWord dR Q hRQ := by
  let : ∀ j, IsAffine ((matchingSingletonCover MN cN hcN).X j) := hWaff
  let s0SAlg : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
  let s0SK : IsScalarTower S₀ S K := Subalgebra.inclusion.isScalarTower_right hS₀ K
  let sRAlg : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let sRK : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let s0RAlg : Algebra S₀ R := (Subalgebra.inclusion (hS₀.trans hSR)).toAlgebra
  let s0RK : IsScalarTower S₀ R K :=
    Subalgebra.inclusion.isScalarTower_right (hS₀.trans hSR) K
  let s0SR : IsScalarTower S₀ S R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have factory := @exists_append_matching_retention.{u} (K := K) (I := input.I) (J := J)
    (kField := kField) (kClosed := kClosed) (kZero := kZero)
    (sComm := inferInstanceAs (CommRing S₀)) (tComm := inferInstanceAs (CommRing S))
    (sTAlg := s0SAlg) (tRAlg := sRAlg)
    (sKAlg := inferInstanceAs (Algebra S₀ K)) (tKAlg := inferInstanceAs (Algebra S K))
    (sTK := s0SK) (tRK := sRK) (jFinite := jFinite)
    (hNopen := @hNopen) (hNdir := hNdir) (hNSep := hSep) (hNSmooth := hSmooth)
    (vFinite := vFinite) (vAffine := vAffine)
    (Y := Y) (Z := Z) (S := S₀) (T := S) (R := R)
    (G := G) (word := word) (i := i)
    (F := input.F) (N := input.N) (e := input.e) (sel := input.sel)
    (V₀ := input.V₀) (p := input.p) (c := input.c)
    (MN := MN) (cN := cN) (hcN := hcN) (delta := delta) (hco := hco) (hnat := hnat)
    (g := input.g) (a₀ := input.a₀) (hend := input.hend)
    (D := old.D) (eP := old.eP) (cD := old.cD)
    (hOpen := old.hOpen) (hCover := old.hCover)
    (base := old.base) (m := old.m) (h₀ := old.hCart)
    (b := input.b) (hbbase := input.hbbase) (hfield := old.hfield) (hprior := old.hprior)
    (baseK := baseK) (E := E) (r := r) (hEr := hEr) (hE := hE)
    (q₁ := d.q) (q₂ := q) (n := n) (m₁ := m) (hn := hn) (hm := d.hm) (hK := hK)
    (V₁ := d.V) (index₁ := d.index) (eV₁ := d.eV) (hV₁ := d.hold)
    (V := V) (index₂ := index) (eV := eV)
    (hV := hV) (hVbase := hVbase) (EL := EL) (hR := hR)
  obtain ⟨Q, hRQ, hQ, hdata⟩ := factory
  obtain ⟨πField, jK, hNative, hword, hπField, hjKb, hcoframes⟩ := hdata
  have hmWord : nWord ≫ q = m := by
    apply (cancel_epi E.hom).mp
    exact ((Category.assoc E.hom nWord q).symm.trans
      (congrArg (fun f => f ≫ q) hWord)).trans hn
  let eFlat : firstChartIsos (A₁ := R) input.N.obj V
      (fun z => ((index.trans d.index) z).1) :=
    fun z => eV z ≪≫ @cancel_chart_iso.{u} S₀ S R (input.N.obj (d.index (index z)).1)
      (inferInstanceAs (CommRing S₀)) (inferInstanceAs (CommRing S))
      (inferInstanceAs (CommRing R))
      (@CommAlgCat.commRing S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index z)).1))
      s0SAlg s0RAlg sRAlg s0SR
      (@CommAlgCat.algebra S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index z)).1))
  let dR : @AppendChartStage.{u} K kField kClosed kZero S₀ G word i R
      (hS₀.trans hSR) input old cN.pt.left cN.pt.hom nWord :=
    @AppendChartStage.mk.{u} K kField kClosed kZero S₀ G word i R
      (hS₀.trans hSR) input old cN.pt.left cN.pt.hom nWord
      (q ≫ d.q)
      ((Category.assoc nWord q d.q).symm.trans
        ((congrArg (fun f => f ≫ d.q) hmWord).trans d.hm))
      V vFinite vAffine (index.trans d.index) eFlat
      (by
        dsimp only
        intro z
        exact join_chart_squares (C := Scheme.{u})
          (d.eV (index z)) (eV z) (@cancel_chart_iso.{u} S₀ S R (input.N.obj (d.index (index z)).1)
      (inferInstanceAs (CommRing S₀)) (inferInstanceAs (CommRing S))
      (inferInstanceAs (CommRing R))
      (@CommAlgCat.commRing S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index z)).1))
      s0SAlg s0RAlg sRAlg s0SR
      (@CommAlgCat.algebra S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index z)).1)))
          (eFlat z)
          rfl (hV z) (d.hold (index z)) (@cancel_chart_pair.{u} S₀ S R (input.N.obj (d.index (index
              z)).1)
            (inferInstanceAs (CommRing S₀)) (inferInstanceAs (CommRing S))
            (inferInstanceAs (CommRing R))
            (@CommAlgCat.commRing S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index
                z)).1))
            s0SAlg s0RAlg sRAlg s0SR
            (@CommAlgCat.algebra S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index
                z)).1))))
      (by
        dsimp only
        intro z
        exact join_chart_base (C := Scheme.{u})
          (eV z) (@cancel_chart_iso.{u} S₀ S R (input.N.obj (d.index (index z)).1)
      (inferInstanceAs (CommRing S₀)) (inferInstanceAs (CommRing S))
      (inferInstanceAs (CommRing R))
      (@CommAlgCat.commRing S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index z)).1))
      s0SAlg s0RAlg sRAlg s0SR
      (@CommAlgCat.algebra S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index z)).1)))
          (eFlat z) rfl (hVbase z) (@cancel_chart_base.{u} S₀ S R (input.N.obj (d.index (index
          z)).1)
            (inferInstanceAs (CommRing S₀)) (inferInstanceAs (CommRing S))
            (inferInstanceAs (CommRing R))
            (@CommAlgCat.commRing S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index
                z)).1))
            s0SAlg s0RAlg sRAlg s0SR
            (@CommAlgCat.algebra S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index
                z)).1))))
  have hspec :
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hSR).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hS₀.trans hSR)).toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have hdR : IsPullback dR.q cN.pt.hom old.base
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hS₀.trans hSR)).toRingHom)) := by
    exact hspec ▸ hq.paste_horiz hdS
  refine ⟨dR, hdR, hCsm, hCommon, Q, hRQ, hQ,
    πField, jK, hNative, hword, ?_, hjKb, hcoframes⟩
  intro z
  exact @scalar_field_chart_equation.{u} S₀ S R K
    (input.N.obj (d.index (index z)).1) (input.F.obj (d.index (index z)).1)
    (inferInstanceAs (CommRing S₀)) (inferInstanceAs (CommRing S))
    (inferInstanceAs (CommRing R)) (@Field.toCommRing K kField)
    (@CommAlgCat.commRing S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index z)).1))
    (@CommAlgCat.commRing K (@Field.toCommRing K kField) (input.F.obj (d.index (index z)).1))
    s0SAlg sRAlg s0RAlg s0SR
    (inferInstanceAs (Algebra S₀ K)) (inferInstanceAs (Algebra S K))
    (inferInstanceAs (Algebra R K)) s0SK sRK s0RK
    (@CommAlgCat.algebra S₀ (inferInstanceAs (CommRing S₀)) (input.N.obj (d.index (index z)).1))
    (@CommAlgCat.algebra K (@Field.toCommRing K kField) (input.F.obj (d.index (index z)).1))
    (input.e (d.index (index z)).1)
    (@scalarDiagramComparison.{u,u,u} K kField S₀ R (hS₀.trans hSR)
      {s : Finset input.I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset input.I // s.Nonempty}))
      input.N input.F input.e (d.index (index z)).1)
    (fun k r a => @scalarDiagramComparison_tmul.{u,u,u} K kField S₀ R (hS₀.trans hSR)
      {s : Finset input.I // s.Nonempty}
      (inferInstanceAs (Category.{u} {s : Finset input.I // s.Nonempty}))
      input.N input.F input.e (d.index (index z)).1 k r a)
    (V.X z) (eV z) (πField z) (hπField z)


end Context






private def fieldSchemeIso {B X : Scheme.{u}} {C : Over B} {b : X ⟶ B}
    (h : C = Over.mk b) : C.left ≅ X := (Over.forget B).mapIso (eqToIso h)

private def fieldSchemeMap {B X Y : Scheme.{u}} {C : Over B} {b : X ⟶ B}
    (h : C = Over.mk b) (n : C.left ⟶ Y) : X ⟶ Y := by
  cases h
  exact n

private theorem fieldSchemeMap_comp {B X Y : Scheme.{u}} {C : Over B} {b : X ⟶ B}
    (h : C = Over.mk b) (n : C.left ⟶ Y) :
    (fieldSchemeIso h).hom ≫ fieldSchemeMap h n = n := by
  cases h
  exact Category.id_comp n

private theorem fieldSchemeIso_base {B X : Scheme.{u}} {C : Over B} {b : X ⟶ B}
    (h : C = Over.mk b) : (fieldSchemeIso h).hom ≫ b = C.hom :=
  (eqToHom h).w

private theorem fieldSchemeIso_left {B X : Scheme.{u}} {C : Over B} {b : X ⟶ B}
    (h : C = Over.mk b) : (fieldSchemeIso h).hom = (eqToHom h).left := rfl



end SchubertGeometry
