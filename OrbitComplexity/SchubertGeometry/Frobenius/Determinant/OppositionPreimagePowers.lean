import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionAffineRefinements
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingStageGeometry
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPreimageRefinements
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.PreimageCoframePowers
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedFrameSquares
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coframe powers on polynomial-chart preimages -/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting ReductiveGroups GroupActions
open FrobeniusSplitting.RetainedCharacter FrobeniusSplitting.CharacterLine
open scoped TensorProduct CategoryTheory.MonObj

noncomputable section

namespace SchubertGeometry.RetainedCharacter

open private FrobeniusSplitting.RetainedCharacter.singletonIndex from
  OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private SchubertGeometry.RetainedCharacter.preimageSnd from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
open private SchubertGeometry.RetainedCharacter.affineChart_base from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCommonCoframes
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private coframeUnit_transport from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCoframePowers

private theorem node_factor {A B C D E F : Scheme.{u}}
    (u : A ⟶ B) (small : B ⟶ C) (leg : C ⟶ D) [hmono : Mono leg]
    (j : B ⟶ D) (hj : j = small ≫ leg)
    (c : A ⟶ E) (legF : E ⟶ F) (v : E ⟶ C) (q : F ⟶ D)
    (hv : v ≫ leg = legF ≫ q) (a : A ⟶ F)
    (hc : c ≫ legF = a) (h : u ≫ j = a ≫ q) :
    u ≫ small = c ≫ v ∧ u ≫ (small ≫ leg) = (c ≫ legF) ≫ q := by
  have ht : u ≫ (small ≫ leg) = (c ≫ legF) ≫ q :=
    (congrArg (fun f => u ≫ f) hj.symm).trans
      (h.trans (congrArg (fun f => f ≫ q) hc.symm))
  refine ⟨(cancel_mono leg).mp ?_, ht⟩
  calc
    (u ≫ small) ≫ leg = u ≫ (small ≫ leg) := Category.assoc _ _ _
    _ = (c ≫ legF) ≫ q := ht
    _ = c ≫ (v ≫ leg) :=
      (Category.assoc _ _ _).trans (congrArg (fun f => c ≫ f) hv.symm)
    _ = (c ≫ v) ≫ leg := (Category.assoc _ _ _).symm

private theorem squareFrame_triangle {A B C Y T : Scheme.{u}}
    (q : T ⟶ Y) (a b : A ⟶ T) (hb : b = a)
    (small : B ⟶ C) (leg : C ⟶ Y) (j : B ⟶ Y)
    (hj : j = small ≫ leg) (u : A ⟶ B)
    (L : Y.Modules)
    (E : (Scheme.Modules.pullback leg).obj L ≅
      SheafOfModules.unit C.ringCatSheaf)
    (h0 : u ≫ (small ≫ leg) = b ≫ q) (h1 : u ≫ j = a ≫ q)
    {F : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback q).obj L) ≅
      SheafOfModules.unit A.ringCatSheaf}
    (hF : F = squareFrameIso q b (small ≫ leg) u h0 L
      (frame_on_composite small leg (small ≫ leg) rfl L E)) :
    F = (Scheme.Modules.pullbackCongr hb).app
        ((Scheme.Modules.pullback q).obj L) ≪≫
      squareFrameIso q a j u h1 L (frame_on_composite small leg j hj L E) := by
  subst j
  subst a
  change F = Iso.refl _ ≪≫ squareFrameIso q b (small ≫ leg) u h1 L
    (frame_on_composite small leg (small ≫ leg) rfl L E)
  exact hF.trans (Iso.refl_trans _).symm

private theorem compositeFrame_triangle {A B C : Scheme.{u}}
    (k : A ⟶ B) (g : B ⟶ C) (j : A ⟶ C) (hj : j = k ≫ g)
    (L : C.Modules)
    (E : (Scheme.Modules.pullback g).obj L ≅
      SheafOfModules.unit B.ringCatSheaf) :
    frame_on_composite k g j hj L E =
      (Scheme.Modules.pullbackCongr hj).app L ≪≫
        frame_on_composite k g (k ≫ g) rfl L E := by
  subst j
  change frame_on_composite k g (k ≫ g) rfl L E =
    Iso.refl _ ≪≫ frame_on_composite k g (k ≫ g) rfl L E
  exact (Iso.refl_trans _).symm

private theorem unit_power_transport (A : Type u) [CommRing A]
    {L M : ℕ → (Spec (.of A)).Modules}
    {E' F' : ∀ n, L n ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf}
    (hpow : ∀ n, affineCoframeUnit A (E' n) (F' n) =
      affineCoframeUnit A (E' 1) (F' 1) ^ n)
    (T : ∀ n, L n ≅ M n)
    (E F : ∀ n, M n ≅ SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    (hE : ∀ n, E' n = T n ≪≫ E n) (hF : ∀ n, F' n = T n ≪≫ F n)
    (n : ℕ) :
    affineCoframeUnit A (E n) (F n) = affineCoframeUnit A (E 1) (F 1) ^ n := by
  have hunit (m : ℕ) : affineCoframeUnit A (E' m) (F' m) =
      affineCoframeUnit A (E m) (F m) :=
    coframeUnit_transport A (T m) (E m) (F m) (E' m) (F' m) (hE m) (hF m)
  exact (hunit n).symm.trans ((hpow n).trans (congrArg (fun c => c ^ n) (hunit 1)))



/-- Ratios of matching coframes and the coframes on polynomial-chart preimages are
powers of their degree-one ratio, on every affine refinement of the matching cover. -/
theorem affinePreimage_coframe_power
    {R K : Type u} [hR : CommRing R]
    [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    [hRK : Algebra R K]
    {J : Type u}
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    (F : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} K)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    [hFopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (F.map f).hom.toRingHom))]
    [hFdir : ((F.op ⋙ algSpec (.of K) ⋙ Over.forget (Spec (.of K))) ⋙
      Scheme.forget).IsLocallyDirected]
    (e : ∀ s, K ⊗[R] N.obj s ≃ₐ[K] F.obj s)
    (v : N ⋙ forget₂ (CommAlgCat R) CommRingCat ⟶
      F ⋙ forget₂ (CommAlgCat K) CommRingCat)
    (hev : ∀ s x, e s ((1 : K) ⊗ₜ[R] x) = (v.app s).hom x)
    (cN : Cocone (N.op ⋙ algSpec (.of R))) (hcN : IsColimit cN)
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
    (i : G.rootBase.support) (P : Scheme.{u}) [hP : IsAffine P]
    (t : P ⟶ wordChartPreimage G word q i) (index : J)
    (Q : Scheme.{u}) (small : Q ⟶ Spec (.of (N.obj
      (FrobeniusSplitting.RetainedCharacter.singletonIndex index))))
    (j : Q ⟶ cN.pt.left) (hsmall : j = small ≫ (cN.ι.app (op
      (FrobeniusSplitting.RetainedCharacter.singletonIndex index))).left)
    (u : Spec (.of Γ(P, ⊤)) ⟶ Q)
    (hscalar : u ≫ j = ((P.isoSpec.inv ≫ t) ≫ (SchubertGeometry.RetainedCharacter.preimageSnd G word
      q i)) ≫ qN)
    (n : ℕ) :
    let : Algebra K Γ(P, ⊤) := ((t ≫ (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫
      cF.pt.hom)).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    affineCoframeUnit Γ(P, ⊤) (squareFrameIso qN ((P.isoSpec.inv ≫ t) ≫
      (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) j u hscalar (matchingModule N cN
      deltaN n) (frame_on_composite small (cN.ι.app (op
      (FrobeniusSplitting.RetainedCharacter.singletonIndex index))).left j hsmall (matchingModule N
      cN deltaN n) (@localCharacterTrivialization R J hR N hNopen hNdir cN hcN deltaN n hcoN hnN
      (FrobeniusSplitting.RetainedCharacter.singletonIndex index) index (Finset.mem_singleton_self
      index)))) (frame_on_composite (P.isoSpec.inv ≫ t)
      (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) ((P.isoSpec.inv ≫ t) ≫
      (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) rfl ((Scheme.Modules.pullback
      qN).obj (matchingModule N cN deltaN n)) (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F
      hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN
      hcN qN hqN hcoN hnN i n)) =
      affineCoframeUnit Γ(P, ⊤) (squareFrameIso qN ((P.isoSpec.inv ≫ t) ≫
        (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) j u hscalar (matchingModule N
        cN deltaN 1) (frame_on_composite small (cN.ι.app (op
        (FrobeniusSplitting.RetainedCharacter.singletonIndex index))).left j hsmall (matchingModule
        N cN deltaN 1) (@localCharacterTrivialization R J hR N hNopen hNdir cN hcN deltaN 1 hcoN hnN
        (FrobeniusSplitting.RetainedCharacter.singletonIndex index) index (Finset.mem_singleton_self
        index)))) (frame_on_composite (P.isoSpec.inv ≫ t)
        (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) ((P.isoSpec.inv ≫ t) ≫
        (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) rfl ((Scheme.Modules.pullback
        qN).obj (matchingModule N cN deltaN 1)) (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F
        hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN
        hcN qN hqN hcoN hnN i 1)) ^ n := by
  let : Algebra K Γ(P, ⊤) := ((t ≫ (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫
    cF.pt.hom)).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  have hfactor : (u ≫ small) ≫ (cN.ι.app (op (FrobeniusSplitting.RetainedCharacter.singletonIndex
    index))).left =
      ((P.isoSpec.inv ≫ t) ≫ (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) ≫ qN :=
    (Category.assoc u small (cN.ι.app (op (FrobeniusSplitting.RetainedCharacter.singletonIndex
      index))).left).trans
      ((congrArg (fun m => u ≫ m) hsmall.symm).trans hscalar)
  obtain ⟨f, hf⟩ := @exists_affine_preimage_refinement.{u} R K hR hK hAlg hChar hRK J N F hNopen
    hNdir e v hev cN hcN cF hcF qN hqN G word q i P hP t index (u ≫ small) hfactor
  have hbase := @SchubertGeometry.RetainedCharacter.affineChart_base K hK.toCommRing P hP (t ≫
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom))
  let D : WordPreimageRefinement G F cF word q i :=
    { ring := CommAlgCat.of K Γ(P, ⊤)
      index := (FrobeniusSplitting.RetainedCharacter.singletonIndex index)
      entry := index
      mem := Finset.mem_singleton_self index
      toChart := f
      toPreimage := P.isoSpec.inv ≫ t
      triangle := hf
      preimageBase := (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) ≫ cF.pt.hom
      lift_over := @wordChartPreimage_base.{u} K hK hAlg hChar G word cF.pt q hword i
      base := (Category.assoc P.isoSpec.inv t ((SchubertGeometry.RetainedCharacter.preimageSnd G
        word q i) ≫ cF.pt.hom)).trans hbase }
  have hnode := node_factor (hmono := (@IsOpenImmersion.mono (Spec (.of (N.obj
    (FrobeniusSplitting.RetainedCharacter.singletonIndex index)))) cN.pt.left (cN.ι.app (op
    (FrobeniusSplitting.RetainedCharacter.singletonIndex index))).left
    ((@SchubertGeometry.retained_prior_charts R hR {s : Finset J // s.Nonempty} (inferInstanceAs
    (Category {s : Finset J // s.Nonempty})) (inferInstanceAs (Quiver.IsThin {s : Finset J //
    s.Nonempty})) (inferInstanceAs (Small.{u} {s : Finset J // s.Nonempty})) N hNopen hNdir cN
    hcN).1 (FrobeniusSplitting.RetainedCharacter.singletonIndex index)))) u small (cN.ι.app (op
    (FrobeniusSplitting.RetainedCharacter.singletonIndex index))).left j hsmall D.toChart.left
    (cF.ι.app (op (FrobeniusSplitting.RetainedCharacter.singletonIndex index))).left
    (Spec.map (v.app (FrobeniusSplitting.RetainedCharacter.singletonIndex index))) qN
    (hqN (FrobeniusSplitting.RetainedCharacter.singletonIndex index)) ((P.isoSpec.inv ≫ t) ≫
      (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) D.triangle hscalar
  have hE (m : ℕ) := squareFrame_triangle qN ((P.isoSpec.inv ≫ t) ≫
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) (D.toChart.left ≫ (cF.ι.app (op
    D.index)).left) D.triangle small (cN.ι.app (op
    (FrobeniusSplitting.RetainedCharacter.singletonIndex index))).left j hsmall u (matchingModule N
    cN deltaN m) (@localCharacterTrivialization R J hR N hNopen hNdir cN hcN deltaN m hcoN hnN
    (FrobeniusSplitting.RetainedCharacter.singletonIndex index) index (Finset.mem_singleton_self
    index)) hnode.2 hscalar (@refinedUnitFrame_scalar R K J hR hK.toCommRing N F hNopen hFopen hNdir
    hFdir cN hcN cF hcF v qN hqN deltaN (@wordTransitionUnit.{u} K hK hAlg hChar G J F beta) hd m
    hcoN hnN hco hn index (Spec (.of Γ(P, ⊤))) Q D.toChart.left small u hnode.1 hnode.2)
  have hF (m : ℕ) := compositeFrame_triangle D.toPreimage
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) (D.toChart.left ≫ (cF.ι.app (op
    D.index)).left) D.triangle ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN m))
    (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha beta
    hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN i m)
  have hfinal := unit_power_transport Γ(P, ⊤) (fun m => @wordPreimage_coframe_power K hK hAlg hChar
    G J F hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd
    cN hcN qN hqN hcoN hnN i D m) (fun m => (Scheme.Modules.pullbackCongr D.triangle).app
    ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN m))) (fun m => (squareFrameIso qN
    ((P.isoSpec.inv ≫ t) ≫ (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) j u hscalar
    (matchingModule N cN deltaN m) (frame_on_composite small (cN.ι.app (op
    (FrobeniusSplitting.RetainedCharacter.singletonIndex index))).left j hsmall (matchingModule N cN
    deltaN m) (@localCharacterTrivialization R J hR N hNopen hNdir cN hcN deltaN m hcoN hnN
    (FrobeniusSplitting.RetainedCharacter.singletonIndex index) index (Finset.mem_singleton_self
    index))))) (fun m => (frame_on_composite (P.isoSpec.inv ≫ t)
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) ((P.isoSpec.inv ≫ t) ≫
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) rfl ((Scheme.Modules.pullback
    qN).obj (matchingModule N cN deltaN m)) (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F
    hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R hR N hNopen hNdir v deltaN hd cN hcN
    qN hqN hcoN hnN i m))) hE hF n
  exact hfinal

end SchubertGeometry.RetainedCharacter
