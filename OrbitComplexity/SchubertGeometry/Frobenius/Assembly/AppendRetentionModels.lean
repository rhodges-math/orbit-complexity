import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Scalar coordinate models of the append charts

The coordinate model retains its flattened chart stage and the field coframes
on that same cover.
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

open private coordinateScalarBase coordinateScalarMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordModelSection
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private matchingCommonField from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingStageGeometry
open private AppendChartData AppendChartData.N
  AppendChartContext AppendChartContext.base
  AppendChartStage AppendChartStage.V AppendChartStage.eV AppendChartStage.index
  AppendChartStage.finite AppendChartStage.affine AppendChartStage.q
  firstCoefficient contextRetentionData retain_chart_context from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendRetentionContexts

section Model

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
    (EA : let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      cN.pt ≅ Over.mk (coordinateScalarBase (R := R) base))
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
    (nWord : bsdhScheme G (word ++ [i]) ⟶ cN.pt.left)

private def modelRetentionResult : Prop :=
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
  let W := matchingSingletonCover MN cN hcN
  let q := EA.hom.left ≫ coordinateScalarMap (R := R) base
  ∃ (hWfinite : Finite W.I₀) (hWaff : ∀ j, IsAffine (W.X j)),
    let : Finite W.I₀ := hWfinite
    let : ∀ j, IsAffine (W.X j) := hWaff
    IsPullback q cN.pt.hom base
      (Spec.map (CommRingCat.ofHom (algebraMap S R))) ∧
    ∃ (hproper : IsProper cN.pt.hom) (hsmooth : Smooth cN.pt.hom)
      (hsep : cN.pt.left.IsSeparated),
      let : IsProper cN.pt.hom := hproper
      let : Smooth cN.pt.hom := hsmooth
      let : cN.pt.left.IsSeparated := hsep
      ∃ dR : @AppendChartStage.{u} K kField kClosed kZero S₀ G word i R
          (hS₀.trans hSR) input old cN.pt.left cN.pt.hom nWord,
        let : ∀ z, IsAffine ((AppendChartStage.V dR).X z) := (AppendChartStage.affine dR)
        IsPullback (AppendChartStage.q dR) cN.pt.hom (AppendChartContext.base old)
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hS₀.trans hSR)).toRingHom)) ∧
        (∀ l, Smooth ((appendCommonCover W (AppendChartStage.V dR)).f l ≫ cN.pt.hom)) ∧
        matchingCommonField Subtype.val_injective cN.pt.hom baseK n hK W (AppendChartStage.V dR) ∧
        ∃ (Q : Subalgebra ℤ K) (hRQ : R ≤ Q), Q.FG ∧
          @contextRetentionData.{u} K kField kClosed kZero G word i S₀ input old R
            (hS₀.trans hSR) J jFinite MN
            @hNopen
            hNdir
            cN hcN hsep delta hco hnat Z baseK n r hK EL nWord dR Q hRQ

private theorem retain_model_coordinates
    (hE : E.hom ≫ bsdhToSpec G (word ++ [i]) = baseK) (hEr : E.hom = r)
    (hproj : let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      n ≫ (EA.hom.left ≫ coordinateScalarMap (R := R) base) = E.hom ≫ m)
    (hR : R.FG)
    (hdS : IsPullback (AppendChartStage.q d) base (AppendChartContext.base old)
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₀).toRingHom)))
    (hWord : E.hom ≫ nWord = n)
    (hcoords :
      let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
      let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
      let : Finite (AppendChartStage.V d).I₀ := (AppendChartStage.finite d)
      matchingModelCoordinates base MN cN hcN EA (AppendChartStage.V d)
        (fun j => (firstCoefficient (A₁ := S) ((AppendChartData.N input).obj
            ((AppendChartStage.index d) j).1)))
        (AppendChartStage.eV d) Subtype.val_injective baseK n hK) :
    @modelRetentionResult.{u} K kField kClosed kZero G word i S S₀ hS₀ input old
      Y base R hSR J jFinite MN
      @hNopen
      hNdir
      cN hcN EA delta hco hnat Z baseK n r hK EL nWord := by
  let : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let : Algebra S₀ S := (Subalgebra.inclusion hS₀).toAlgebra
  let : Finite (AppendChartStage.V d).I₀ := (AppendChartStage.finite d)
  obtain ⟨hWfinite, hWaff, hCart, hproper, hsmooth, hsep, V, hfinite, haff,
    index, eV, hVbase, hVold, hCsm, hCommon⟩ := hcoords
  let : Smooth cN.pt.hom := hsmooth
  let : cN.pt.left.IsSeparated := hsep
  let : Finite V.I₀ := hfinite
  let : ∀ j, IsAffine (V.X j) := haff
  obtain ⟨dR, hdR, hCsmR, hCommonR, Q, hRQ, hQ, hdata⟩ :=
    @retain_chart_context.{u} K kField kClosed kZero G word i S S₀ hS₀ input old
      Y base m d R hSR J jFinite MN
      @hNopen
      hNdir
      cN hcN hsep hsmooth delta hco hnat Z baseK n r hK EL E
      V hfinite haff index eV
      (EA.hom.left ≫ coordinateScalarMap (R := R) base) nWord hWord hdS hCart
      hE hEr hproj hVold hVbase hR hWaff hCsm hCommon
  exact ⟨hWfinite, hWaff, hCart, hproper, hsmooth, hsep,
    dR, hdR, hCsmR, hCommonR, Q, hRQ, hQ, hdata⟩

end Model


end SchubertGeometry
