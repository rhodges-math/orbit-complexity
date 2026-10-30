import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPreimageStages
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.PreimageChartCoordinates
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCoverCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCoframeGluing
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CartesianCoframeComparison
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameSquareRebase
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coframes on opposite-chart preimages -/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting ReductiveGroups GroupActions
open FrobeniusSplitting.RetainedCharacter FrobeniusSplitting.CharacterLine
open scoped TensorProduct CategoryTheory.MonObj

noncomputable section

namespace SchubertGeometry.RetainedCharacter

open private FrobeniusSplitting.RetainedCharacter.singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private SchubertGeometry.RetainedCharacter.preimageSnd from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private affineChartPullback from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.PreimageChartCoordinates
open private scalarMap scalarMap_factor extendedFrame from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private compositeFrame_rfl from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedFrameSquares
open private wholeComparison refinement_cancel from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes

private theorem coordinate_square {S T K : Type u}
    [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {X P Y YK : Scheme.{u}} [IsAffine X] [IsAffine P]
    [Algebra S Γ(X, ⊤)] [Algebra K Γ(P, ⊤)]
    (g : X ⟶ Y) (a : P ⟶ YK) (p : P ⟶ X) (m : YK ⟶ Y)
    (h : p ≫ g = a ≫ m) (e : K ⊗[S] Γ(X, ⊤) ≃ₐ[K] Γ(P, ⊤))
    (he : ∀ x, e ((1 : K) ⊗ₜ[S] x) = p.appTop.hom x) :
    Spec.map (CommRingCat.ofHom (scalarMap (R := T) e)) ≫
        ((Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : Γ(X, ⊤) →ₐ[S] T ⊗[S] Γ(X, ⊤)).toRingHom) ≫
            X.isoSpec.inv) ≫ g) = (P.isoSpec.inv ≫ a) ≫ m := by
  have hring := scalarMap_factor (R := T) e p.appTop.hom he
  have hspec :
      Spec.map (CommRingCat.ofHom (scalarMap (R := T) e)) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : Γ(X, ⊤) →ₐ[S] T ⊗[S] Γ(X, ⊤)).toRingHom) =
      Spec.map p.appTop := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact DFunLike.congr_fun hring x
  calc
    _ = (Spec.map p.appTop ≫ X.isoSpec.inv) ≫ g := by
      rw [← Category.assoc, ← Category.assoc, hspec]
    _ = (P.isoSpec.inv ≫ p) ≫ g := by rw [Scheme.isoSpec_inv_naturality p]
    _ = _ := by simp only [Category.assoc, h]

private theorem preimage_square {Y YK P PK A B : Scheme.{u}}
    (q : YK ⟶ Y) (f : P ⟶ Y) (g : PK ⟶ YK) (z : PK ⟶ P)
    (a : A ⟶ PK) (b : B ⟶ P) (u : A ⟶ B)
    (hwhole : z ≫ f = g ≫ q) (hsmall : u ≫ b = a ≫ z)
    (jB : B ⟶ Y) (hjB : jB = b ≫ f)
    (htotal : u ≫ jB = (a ≫ g) ≫ q) (L : Y.Modules)
    (E : (Scheme.Modules.pullback jB).obj L ≅
      SheafOfModules.unit B.ringCatSheaf)
    (FK : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback q).obj L) ≅
      SheafOfModules.unit PK.ringCatSheaf)
    (he : squareFrameIso q (a ≫ g) jB u htotal L E =
      frame_on_composite a g (a ≫ g) rfl ((Scheme.Modules.pullback q).obj L) FK) :
    squareFrameIso z a b u hsmall ((Scheme.Modules.pullback f).obj L)
        ((pullbackComp b f).app L ≪≫ (pullbackCongr hjB.symm).app L ≪≫ E) =
      (Scheme.Modules.pullback a).mapIso
        (wholeComparison q f g z hwhole L ≪≫ FK) ≪≫ pullbackObjUnitIso a := by
  subst jB
  change squareFrameIso z a b u hsmall ((Scheme.Modules.pullback f).obj L)
      ((pullbackComp b f).app L ≪≫ E) = _
  rw [squareFrameIso_rebase q f g z a b u hwhole hsmall htotal L E, he,
    compositeFrame_rfl]
  exact refinement_cancel (Scheme.Modules.pullback a)
    ((pullbackComp z f).app L ≪≫ (pullbackCongr hwhole).app L ≪≫
      ((pullbackComp g q).app L).symm) FK
    ((pullbackComp a g).app ((Scheme.Modules.pullback q).obj L))
    (pullbackObjUnitIso a)

private theorem scalar_cover_glue {S T K : Type u}
    [hS : CommRing S] [hT : CommRing T] [hK : CommRing K]
    [hST : Algebra S T] [hSK : Algebra S K] [hTK : Algebra T K]
    [hSTK : IsScalarTower S T K] (hi : Function.Injective (algebraMap T K))
    {Y YT YK : Scheme.{u}} [hYT : YT.IsSeparated]
    (base : Y ⟶ Spec (.of S)) (baseT : YT ⟶ Spec (.of T)) [hSmooth : Smooth baseT]
    (baseK : YK ⟶ Spec (.of K)) (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y)
    (hbase : n ≫ q = m)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hn : IsPullback n baseK baseT (Spec.map (CommRingCat.ofHom (algebraMap T K))))
    (V : Y.OpenCover.{u}) [hV : ∀ l, IsAffine (V.X l)]
    (P : V.I₀ → Scheme.{u}) [hP : ∀ l, IsAffine (P l)]
    (a : ∀ l, P l ⟶ YK) (p : ∀ l, P l ⟶ V.X l)
    (hcart : ∀ l, IsPullback (p l) (a l) (V.f l) m) :
    letI : ∀ l, Algebra S Γ(V.X l, ⊤) := fun l =>
      ((V.f l ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    letI : ∀ l, Algebra K Γ(P l, ⊤) := fun l =>
      ((a l ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∀ (e : ∀ l, K ⊗[S] Γ(V.X l, ⊤) ≃ₐ[K] Γ(P l, ⊤))
      (_he : ∀ l x, e l ((1 : K) ⊗ₜ[S] x) = (p l).appTop.hom x)
      (b : ∀ l, Spec (.of (T ⊗[S] Γ(V.X l, ⊤))) ⟶ Y)
      (_hb : ∀ l, (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        (V.X l).isoSpec.inv) ≫ V.f l = b l)
      (v : ∀ l, Spec Γ(P l, ⊤) ⟶ Spec (.of (T ⊗[S] Γ(V.X l, ⊤))))
      (_hv : ∀ l, v l = Spec.map (CommRingCat.ofHom (scalarMap (R := T) (e l))))
      (aQ : ∀ l, Spec Γ(P l, ⊤) ⟶ YK)
      (_haQ : ∀ l, (@Scheme.isoSpec (P l) (hP l)).inv ≫ a l = aQ l)
      (L : Y.Modules)
      (FK : (Scheme.Modules.pullback m).obj L ≅ SheafOfModules.unit YK.ringCatSheaf)
      (E : ∀ l, (Scheme.Modules.pullback (b l)).obj L ≅
        SheafOfModules.unit (Spec (.of (T ⊗[S] Γ(V.X l, ⊤)))).ringCatSheaf)
      (hscalar : ∀ l, v l ≫ b l = aQ l ≫ m)
      (_hcompare : ∀ l, squareFrameIso m (aQ l) (b l) (v l) (hscalar l) L (E l) =
        (Scheme.Modules.pullback (aQ l)).mapIso FK ≪≫ pullbackObjUnitIso (aQ l)),
      ∃ ET : (Scheme.Modules.pullback q).obj L ≅ SheafOfModules.unit YT.ringCatSheaf,
        (Scheme.Modules.pullback n).mapIso ET ≪≫ pullbackObjUnitIso n =
          ((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫ FK := by
  classical
  let hM : ∀ l, Algebra S Γ(V.X l, ⊤) := fun l =>
    ((V.f l ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let hA : ∀ l, Algebra K Γ(P l, ⊤) := fun l =>
    ((a l ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  intro e he b hb v hv aQ haQ L FK E hscalar hcompare
  let hqAffine : IsAffineHom q :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hq.flip inferInstance
  have hlocal (l : V.I₀) := @exists_scalar_cover_coframe S T K hS hT hK
    hST hSK hTK hSTK Y YT YK (V.X l) ((V.pullback₂ q).X l) (P l) (hV l) (hP l)
    base baseT baseK q n m hbase hq hn.w (V.f l) ((V.pullback₂ q).f l)
    (pullback.fst (V.f l) q) (IsPullback.of_hasPullback (V.f l) q)
    (a l) (p l) (hcart l) (e l) (he l) (b l) (hb l) (v l) (hv l)
    (aQ l) (haQ l) L (E l)
    ((Scheme.Modules.pullback (aQ l)).mapIso FK ≪≫ pullbackObjUnitIso (aQ l))
    (hscalar l) (hcompare l)
  choose k hk0 hk1 hcartT hsquare ET hET using hlocal
  have hcartQ (l : V.I₀) :
      IsPullback ((@Scheme.isoSpec (P l) (hP l)).inv ≫ k l) (aQ l) ((V.pullback₂ q).f l) n :=
    (hcartT l).of_iso' (@Scheme.isoSpec (P l) (hP l)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id])
      (by simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using haQ l)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
  let FT := ((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫ FK
  have hET' (l : V.I₀) :
      squareFrameIso n (aQ l) ((V.pullback₂ q).f l) ((@Scheme.isoSpec (P l) (hP l)).inv ≫ k l)
        (hcartQ l).w ((Scheme.Modules.pullback q).obj L) (ET l) =
      (Scheme.Modules.pullback (aQ l)).mapIso FT ≪≫ pullbackObjUnitIso (aQ l) := by
    calc
      _ = (Scheme.Modules.pullback (aQ l)).mapIso
            ((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫
              (Scheme.Modules.pullback (aQ l)).mapIso FK ≪≫ pullbackObjUnitIso (aQ l) :=
        hET l
      _ = ((Scheme.Modules.pullback (aQ l)).mapIso
              ((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫
            (Scheme.Modules.pullback (aQ l)).mapIso FK) ≪≫ pullbackObjUnitIso (aQ l) :=
        (Iso.trans_assoc _ _ _).symm
      _ = _ := congrArg (fun e => e ≪≫ pullbackObjUnitIso (aQ l))
        (Functor.mapIso_trans (Scheme.Modules.pullback (aQ l))
          ((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) FK).symm
  obtain ⟨F, hF⟩ := scalarCoframe_glue hi baseT baseK n hn
    (V.pullback₂ q)
    (fun l => @affineChartPullback (V.X l) YT Y (V.f l) q (hV l) hqAffine)
    (fun l => Spec Γ(P l, ⊤)) aQ
    (fun l => (@Scheme.isoSpec (P l) (hP l)).inv ≫ k l) hcartQ ((Scheme.Modules.pullback q).obj L)
      FT ET hET'
  refine ⟨F, ?_⟩
  exact scalarCoframe_eq_of_squares n (V.pullback₂ q) (fun l => Spec Γ(P l, ⊤)) aQ
    (fun l => (@Scheme.isoSpec (P l) (hP l)).inv ≫ k l) hcartQ ((Scheme.Modules.pullback q).obj L) F
      FT ET
    (fun l => (hF l).1) hET'

/-- A single coefficient extension admits coframes of every original matching line on
any scalar preimage model, with the prescribed characteristic-zero coframes. -/
theorem exists_preimage_coframes
    {K : Type u}
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (R0 : Subalgebra ℤ K)
    {J : Type u}
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R0)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R0) ⋙ Over.forget (Spec (.of R0))) ⋙
      Scheme.forget).IsLocallyDirected]
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (e : ∀ s, K ⊗[R0] N.obj s ≃ₐ[K] F.obj s)
    (v : N ⋙ forget₂ (CommAlgCat R0) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (hev : ∀ s x, e s ((1 : K) ⊗ₜ[R0] x) = (v.app s).hom x)
    (cN : Cocone (N.op ⋙ algSpec (.of R0))) (hcN : IsColimit cN)
    (cF : Cocone (F.op ⋙ algSpec (.of K))) (hcF : IsColimit cF)
    (qN : cF.pt.left ⟶ cN.pt.left)
    (hqN : ∀ s, Spec.map (v.app s) ≫ (cN.ι.app (op s)).left =
      (cF.ι.app (op s)).left ≫ qN)
    (G : ReductiveGroupData K) (word : List G.rootBase.support)
    (q : cF.pt.left ⟶ bsdhScheme G word)
    (hword : q ≫ bsdhToSpec G word = cF.pt.hom)
    (point : J → G.points)
    (a : ∀ j, (algSpec (.of K)).obj
      (op (F.obj (FrobeniusSplitting.RetainedCharacter.singletonIndex j))) ⟶
        (oppositeUnipotentVariety G).toOver)
    (ha : ∀ j, (a j).left ≫ (flagChartMorphism G (point j)).left =
      (cF.ι.app (op (FrobeniusSplitting.RetainedCharacter.singletonIndex j))).left ≫
        (q ≫ bsdhMap G word))
    (beta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val) (k : J) (_ : k ∈ s.val),
      (algSpec (.of K)).obj (op (F.obj s)) ⟶ (borelVariety G).toOver)
    (hgroup : ∀ s j hj k hk, @chartLift.{u} K hK hAlg hChar G J F point a s j hj =
      @chartLift.{u} K hK hAlg hChar G J F point a s k hk * (beta s j hj k hk ≫ borelInclusion G))
    (hco : ∀ s j hj k hk l hl, @wordTransitionUnit.{u} K hK hAlg hChar G J F beta s j hj l hl =
      @wordTransitionUnit.{u} K hK hAlg hChar G J F beta s k hk l hl *
        @wordTransitionUnit.{u} K hK hAlg hChar G J F beta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (F.map f).hom.toMonoidHom
        (@wordTransitionUnit.{u} K hK hAlg hChar G J F beta s j hj k hk) =
          @wordTransitionUnit.{u} K hK hAlg hChar G J F beta t j ((leOfHom f) hj) k ((leOfHom f)
            hk))
    (deltaN : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val) (k : J) (_ : k ∈ s.val),
      (N.obj s)ˣ)
    (hd : ∀ s j hj k hk, (v.app s).hom (deltaN s j hj k hk : N.obj s) =
      (@wordTransitionUnit.{u} K hK hAlg hChar G J F beta s j hj k hk : F.obj s))
    (hcoN : ∀ s j hj k hk l hl,
      deltaN s j hj l hl = deltaN s k hk l hl * deltaN s j hj k hk)
    (hnN : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (deltaN s j hj k hk) =
        deltaN t j ((leOfHom f) hj) k ((leOfHom f) hk))
    (i : G.rootBase.support) (B : Subalgebra ℤ K) (hB : B.FG)
    {Y0 : Scheme.{u}} [hcompact : CompactSpace Y0]
    (base0 : Y0 ⟶ Spec (.of B)) [hsmooth : Smooth base0]
    (z : wordChartPreimage G word q i ⟶ Y0)
    (hz : IsPullback z
      (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom)
      base0 (Spec.map (CommRingCat.ofHom (algebraMap B K))))
    (j0 : Y0 ⟶ cN.pt.left)
    (hwhole : z ≫ j0 = SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ qN)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ (Tstage : Subalgebra ℤ K) (hBT : B ≤ Tstage),
      start ≤ Tstage ∧ Tstage.FG ∧
      letI : Algebra B Tstage := (Subalgebra.inclusion hBT).toAlgebra
      letI : IsScalarTower B Tstage K := Subalgebra.inclusion.isScalarTower_right hBT K
      ∀ (YT : Scheme.{u}) [YT.IsSeparated]
        (baseT : YT ⟶ Spec (.of Tstage)) [Smooth baseT]
        (qT : YT ⟶ Y0) (nT : wordChartPreimage G word q i ⟶ YT)
        (hbase : nT ≫ qT = z)
        (_hqT : IsPullback qT baseT base0
          (Spec.map (CommRingCat.ofHom (algebraMap B Tstage))))
        (_hnT : IsPullback nT
          (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom)
          baseT (Spec.map (CommRingCat.ofHom (algebraMap Tstage K))))
        (n : ℕ),
        ∃ E : (Scheme.Modules.pullback qT).obj
            ((Scheme.Modules.pullback j0).obj (matchingModule N cN deltaN n)) ≅ SheafOfModules.unit
              YT.ringCatSheaf,
          (Scheme.Modules.pullback nT).mapIso E ≪≫ pullbackObjUnitIso nT =
            ((pullbackComp nT qT).app ((Scheme.Modules.pullback j0).obj (matchingModule N cN deltaN
              n)) ≪≫
              (pullbackCongr hbase).app ((Scheme.Modules.pullback j0).obj (matchingModule N cN
                deltaN n))) ≪≫
                wholeComparison qN j0
                  (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) z hwhole
                    (matchingModule N cN deltaN n) ≪≫
                    (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q
                      point a ha beta hgroup hco hn R0 (inferInstanceAs (CommRing R0)) N hNopen
                      hNdir v deltaN hd cN hcN qN hqN hcoN hnN i n) := by
  classical
  obtain ⟨V, hfinite, haffine, index, b, hb, hcoords⟩ :=
    @exists_preimage_chart_coordinates R0 J (inferInstanceAs (CommRing R0))
      N hNopen hNdir cN hcN
      deltaN hcoN hnN B K (inferInstanceAs (CommRing B)) hK.toCommRing
      (inferInstanceAs (Algebra B K)) (show Function.Injective (algebraMap B K) from
        Subtype.val_injective)
      Y0 (wordChartPreimage G word q i) hcompact base0 hsmooth
      (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom) z hz j0
  let : Finite V.I₀ := hfinite
  let : ∀ l, IsAffine (V.X l) := haffine
  let : IsAffineHom z := MorphismProperty.of_isPullback (P := @IsAffineHom) hz.flip
    inferInstance
  let P : V.I₀ → Scheme.{u} := fun l => pullback (V.f l) z
  let hP : ∀ l, IsAffine (P l) := fun l =>
    @affineChartPullback (V.X l) (wordChartPreimage G word q i) Y0 (V.f l) z
      (haffine l) (inferInstanceAs (IsAffineHom z))
  let hM : ∀ l, Algebra B Γ(V.X l, ⊤) := fun l =>
    ((V.f l ≫ base0).appTop.hom.comp (Scheme.ΓSpecIso (.of B)).inv.hom).toAlgebra
  let hA : ∀ l, Algebra K Γ(P l, ⊤) := fun l =>
    ((pullback.snd (V.f l) z ≫
      (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom)).appTop.hom.comp
        (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let : ∀ l, Module.Flat B Γ(V.X l, ⊤) := fun l => (hcoords l).1
  let : ∀ l, Algebra.FinitePresentation B Γ(V.X l, ⊤) := fun l => (hcoords l).2.1
  choose eA heA hscalarA using fun l => (hcoords l).2.2.2.2
  have hsmall (l : V.I₀) : (V.X l).isoSpec.inv ≫ (V.f l ≫ j0) =
      ((V.X l).isoSpec.inv ≫ b l) ≫
        (cN.ι.app (op (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l)))).left :=
    (hcoords l).2.2.2.1.symm
  have hscalar (l : V.I₀) :
      Spec.map (CommRingCat.ofHom ((eA l).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)) ≫
          ((V.X l).isoSpec.inv ≫ (V.f l ≫ j0)) =
        (((P l).isoSpec.inv ≫ pullback.snd (V.f l) z) ≫
          SchubertGeometry.RetainedCharacter.preimageSnd G word q i) ≫ qN := by
    simpa only [hwhole, Category.assoc] using hscalarA l
  have hfactory := @exists_preimage_power_stage.{u} K hK hAlg hChar R0 J N F
    hNopen hNdir hFopen hFdir e v hev cN hcN cF hcF qN hqN G word q hword
    point a ha beta hgroup hco hn deltaN hd hcoN hnN i B hB
    V.I₀ hfinite P hP (fun l => pullback.snd (V.f l) z)
  obtain ⟨Tstage, hBT, hstartT, hstages⟩ := @hfactory
    (fun l => Γ(V.X l, ⊤)) (fun l => inferInstance) hM
    (fun l => inferInstance) (fun l => inferInstance) eA
    (fun l => (V.X l).isoSpec.inv ≫ (V.f l ≫ j0)) index
    (fun l => (V.X l).isoSpec.inv ≫ b l) hsmall hscalar start hstart
  refine ⟨Tstage, hBT, hstartT, (hstages 0).1, ?_⟩
  let hBTAlg : Algebra B Tstage := (Subalgebra.inclusion hBT).toAlgebra
  let hBTower : IsScalarTower B Tstage K := Subalgebra.inclusion.isScalarTower_right hBT K
  intro YT hYT baseT hSmooth qT nT hbase hqT hnT n
  obtain ⟨d, _, _, hframes⟩ := (hstages n).2
  let Eold (l : V.I₀) := @frame_on_composite
    (Spec (.of Γ(V.X l, ⊤)))
    (Spec (.of (N.obj
      (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l))))) cN.pt.left
    ((V.X l).isoSpec.inv ≫ b l)
    (cN.ι.app (op (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l)))).left
    ((V.X l).isoSpec.inv ≫ (V.f l ≫ j0)) (hsmall l) (matchingModule N cN deltaN n)
    (@localCharacterTrivialization R0 J (inferInstanceAs (CommRing R0))
      N hNopen hNdir cN hcN
      deltaN n hcoN hnN (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l))
      (index l) (Finset.mem_singleton_self (index l)))
  let Eret (l : V.I₀) := adjustedCoframe
    (extendedFrame Algebra.TensorProduct.includeRight.toRingHom
      ((V.X l).isoSpec.inv ≫ (V.f l ≫ j0)) (matchingModule N cN deltaN n) (Eold l)) (d l)
  let bT (l : V.I₀) : Spec (.of (Tstage ⊗[B] Γ(V.X l, ⊤))) ⟶ Y0 :=
    (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
      (V.X l).isoSpec.inv) ≫ V.f l
  have hbT (l : V.I₀) :
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        ((V.X l).isoSpec.inv ≫ (V.f l ≫ j0)) = bT l ≫ j0 := by
    simp only [bT, Category.assoc]
  let F0 := wholeComparison qN j0
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) z hwhole (matchingModule N cN deltaN
      n) ≪≫ (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha
      beta hgroup hco hn R0 (inferInstanceAs (CommRing R0)) N hNopen hNdir v deltaN hd cN hcN qN hqN
      hcoN hnN i n)
  let E0 (l : V.I₀) := (pullbackComp (bT l) j0).app (matchingModule N cN deltaN n) ≪≫
    (pullbackCongr (hbT l).symm).app (matchingModule N cN deltaN n) ≪≫ Eret l
  have htotal0 (l : V.I₀) := @coordinate_square B Tstage K
    (inferInstanceAs (CommRing B)) (inferInstanceAs (CommRing Tstage)) hK.toCommRing
    hBTAlg (inferInstanceAs (Algebra B K)) (inferInstanceAs (Algebra Tstage K)) hBTower
    (V.X l) (P l) Y0 (wordChartPreimage G word q i)
    (haffine l) (hP l) (hM l) (hA l)
    (V.f l) (pullback.snd (V.f l) z) (pullback.fst (V.f l) z) z
    (IsPullback.of_hasPullback (V.f l) z).w (eA l) (heA l)
  have hcompare0 (l : V.I₀) := preimage_square qN j0
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) z
    ((P l).isoSpec.inv ≫ pullback.snd (V.f l) z) (bT l)
    (Spec.map (CommRingCat.ofHom (scalarMap (R := Tstage) (eA l)))) hwhole (htotal0 l)
    (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
      ((V.X l).isoSpec.inv ≫ (V.f l ≫ j0))) (hbT l) (hframes l).choose (matchingModule N cN deltaN
        n)
    (Eret l) (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a
      ha beta hgroup hco hn R0 (inferInstanceAs (CommRing R0)) N hNopen hNdir v deltaN hd cN hcN qN
      hqN hcoN hnN i n) (hframes l).choose_spec
  exact @scalar_cover_glue B Tstage K
    (inferInstanceAs (CommRing B)) (inferInstanceAs (CommRing Tstage)) hK.toCommRing
    hBTAlg (inferInstanceAs (Algebra B K)) (inferInstanceAs (Algebra Tstage K)) hBTower
    (show Function.Injective (algebraMap Tstage K) from Subtype.val_injective)
    Y0 YT (wordChartPreimage G word q i) hYT base0 baseT hSmooth
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom)
    qT nT z hbase hqT hnT V haffine P hP
    (fun l => pullback.snd (V.f l) z) (fun l => pullback.fst (V.f l) z)
    (fun l => IsPullback.of_hasPullback (V.f l) z)
    eA heA bT (fun _ => rfl)
    (fun l => Spec.map (CommRingCat.ofHom (scalarMap (R := Tstage) (eA l))))
    (fun _ => rfl) (fun l => (P l).isoSpec.inv ≫ pullback.snd (V.f l) z) (fun _ => rfl)
    ((Scheme.Modules.pullback j0).obj (matchingModule N cN deltaN n)) F0 E0 htotal0 hcompare0

end SchubertGeometry.RetainedCharacter
