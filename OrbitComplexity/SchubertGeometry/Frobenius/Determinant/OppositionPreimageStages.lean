import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPreimagePowers
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionPreimageUnits
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.CoframeAdjustmentPowers
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Simultaneous retention of coframes on polynomial-chart preimages -/

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
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase

/-- One coefficient stage retains the polynomial-chart preimage coframes in
all character degrees on the original matching line. -/
theorem exists_preimage_power_stage
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
    {I : Type u} [hI : Finite I]
    (P : I → Scheme.{u}) [hP : ∀ l, IsAffine (P l)]
    (t : ∀ l, P l ⟶ wordChartPreimage G word q i) :
    letI _hA : ∀ l, Algebra K Γ(P l, ⊤) := fun l => ((t l ≫
      (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom)).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∀ (M : I → Type u) [_hM : ∀ l, CommRing (M l)]
      [_hBM : ∀ l, Algebra B (M l)] [_hflat : ∀ l, Module.Flat B (M l)]
      [_hfp : ∀ l, Algebra.FinitePresentation B (M l)]
      (eA : ∀ l, K ⊗[B] M l ≃ₐ[K] Γ(P l, ⊤))
      (j : ∀ l, Spec (.of (M l)) ⟶ cN.pt.left) (index : I → J)
      (small : ∀ l, Spec (.of (M l)) ⟶ Spec (.of (N.obj
        (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l)))))
      (hsmall : ∀ l, j l = small l ≫ (cN.ι.app (op
        (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l)))).left)
      (hscalar : ∀ l, Spec.map (CommRingCat.ofHom ((eA l).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)) ≫ j l =
        (((P l).isoSpec.inv ≫ t l) ≫ (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) ≫
          qN)
      (start : Subalgebra ℤ K) (_hstart : start.FG),
      ∃ (Tstage : Subalgebra ℤ K) (hBT : B ≤ Tstage), start ≤ Tstage ∧
        ∀ n, coframeAdjustmentStage B M (fun l => Γ(P l, ⊤)) eA
          (fun l => ((eA l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) qN
            (matchingModule N cN deltaN n) j
          (fun l => ((P l).isoSpec.inv ≫ t l) ≫ (SchubertGeometry.RetainedCharacter.preimageSnd G
            word q i)) hscalar
          (fun l => (@frame_on_composite (Spec (.of (M l))) (Spec (.of (N.obj
            (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l))))) cN.pt.left (small l)
            (cN.ι.app (op (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l)))).left (j
            l) (hsmall l) (matchingModule N cN deltaN n) (@localCharacterTrivialization R0 J
            (inferInstanceAs (CommRing R0)) N hNopen hNdir cN hcN deltaN n hcoN hnN
            (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l)) (index l)
            (Finset.mem_singleton_self (index l))))) (fun l => (@frame_on_composite (Spec (.of Γ(P
            l, ⊤))) (wordChartPreimage G word q i) cF.pt.left ((P l).isoSpec.inv ≫ t l)
            (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) (((P l).isoSpec.inv ≫ t l) ≫
            (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) rfl
            ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN n))
            (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir cF hcF word q point a ha
            beta hgroup hco hn R0 (inferInstanceAs (CommRing R0)) N hNopen hNdir v deltaN hd cN hcN
            qN hqN hcoN hnN i n))) Tstage hBT := by
  let hA : ∀ l, Algebra K Γ(P l, ⊤) := fun l => ((t l ≫
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i ≫ cF.pt.hom)).appTop.hom.comp
    (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  intro M hM hBM hflat hfp eA j index small hsmall hscalar start hstart
  obtain ⟨Tstage, hBT, hstartT, hstage⟩ := @exists_preimage_coframe_units.{u, u} K hK hAlg hChar G J
    F hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R0 N hNopen hNdir v deltaN hd cN hcN
    qN hqN hcoN hnN i B hB I hI M (fun l => Γ(P l, ⊤)) hM hBM hflat hfp (fun l => inferInstanceAs
    (CommRing Γ(P l, ⊤))) hA eA j (fun l => ((P l).isoSpec.inv ≫ t l)) index small hsmall hscalar
    start hstart
  let hBTAlg : Algebra B Tstage := (Subalgebra.inclusion hBT).toAlgebra
  let hBTower : IsScalarTower B Tstage K := Subalgebra.inclusion.isScalarTower_right hBT K
  have hratio (n : ℕ) (l : I) := @affinePreimage_coframe_power.{u} R0 K (inferInstanceAs (CommRing
    R0)) hK hAlg hChar (inferInstanceAs (Algebra R0 K)) J N F hNopen hNdir hFopen hFdir e v hev cN
    hcN cF hcF qN hqN G word q hword point a ha beta hgroup hco hn deltaN hd hcoN hnN i (P l) (hP l)
    (t l) (index l) (Spec (.of (M l))) (small l) (j l) (hsmall l) (Spec.map (CommRingCat.ofHom ((eA
    l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))) (hscalar l) n
  obtain ⟨d, hd, hdata⟩ := @FrobeniusSplitting.RetainedCharacter.coframeAdjustments_powers.{u, u} B
    Tstage K (inferInstanceAs (CommRing B)) (inferInstanceAs (CommRing Tstage)) hK.toCommRing hBTAlg
    (inferInstanceAs (Algebra B K)) (inferInstanceAs (Algebra Tstage K)) hBTower I M (fun l => Γ(P
    l, ⊤)) hM hBM (fun l => inferInstanceAs (CommRing Γ(P l, ⊤))) hA eA (fun l => ((eA
    l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) cN.pt.left cF.pt.left qN (fun n
    => (matchingModule N cN deltaN n)) j (fun l => ((P l).isoSpec.inv ≫ t l) ≫
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) hscalar (fun n l =>
    (@frame_on_composite (Spec (.of (M l))) (Spec (.of (N.obj
    (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l))))) cN.pt.left (small l)
    (cN.ι.app (op (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l)))).left (j l)
    (hsmall l) (matchingModule N cN deltaN n) (@localCharacterTrivialization R0 J (inferInstanceAs
    (CommRing R0)) N hNopen hNdir cN hcN deltaN n hcoN hnN
    (FrobeniusSplitting.RetainedCharacter.singletonIndex (index l)) (index l)
    (Finset.mem_singleton_self (index l))))) (fun n l => (@frame_on_composite (Spec (.of Γ(P l, ⊤)))
    (wordChartPreimage G word q i) cF.pt.left ((P l).isoSpec.inv ≫ t l)
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i) (((P l).isoSpec.inv ≫ t l) ≫
    (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)) rfl ((Scheme.Modules.pullback
    qN).obj (matchingModule N cN deltaN n)) (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F
    hFopen hFdir cF hcF word q point a ha beta hgroup hco hn R0 (inferInstanceAs (CommRing R0)) N
    hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN i n))) (fun l x => rfl) hstage.2 hratio
  exact ⟨Tstage, hBT, hstartT, fun n => ⟨hstage.1, hdata n⟩⟩

end SchubertGeometry.RetainedCharacter
