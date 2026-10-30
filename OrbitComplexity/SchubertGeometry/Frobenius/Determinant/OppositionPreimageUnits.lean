import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage
import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionQuadraticUnits
import OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits

/-! # Retaining coframe units on an opposition-chart preimage

The ratios between the matching coframes and the opposition-chart preimage
coframe, together with their inverses, are defined over one finite coefficient
extension. The coefficient extension can contain any prescribed finite stage.
-/

set_option autoImplicit false
noncomputable section
universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct CategoryTheory.MonObj

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private scalarMap adjustedFamilyData adjustments_of_units from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private SchubertGeometry.DeterminantSection.scalar_extension from
  OrbitComplexity.SchubertGeometry.Frobenius.Determinant.OppositionQuadraticUnits
open private SchubertGeometry.RetainedCharacter.preimageSnd from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordChartPreimage

private theorem retain_above {K : Type u} [hK : Field K]
    (S : Subalgebra ℤ K) (hS : S.FG) {I : Type v} [hI : Finite I]
    (M A : I → Type u)
    [hMring : ∀ i, CommRing (M i)] [hMalgebra : ∀ i, Algebra S (M i)]
    [hFlat : ∀ i, Module.Flat S (M i)] [hFP : ∀ i, Algebra.FinitePresentation S (M i)]
    [hAring : ∀ i, CommRing (A i)] [hAalgebra : ∀ i, Algebra K (A i)]
    (e : ∀ i, K ⊗[S] M i ≃ₐ[K] A i) (v₀ : ∀ i, M i →+* A i)
    (he : ∀ i x, e i ((1 : K) ⊗ₜ[S] x) = v₀ i x)
    {Y YK : Scheme.{u}} (q : YK ⟶ Y) (L : Y.Modules)
    (j : ∀ i, Spec (.of (M i)) ⟶ Y) (a : ∀ i, Spec (.of (A i)) ⟶ YK)
    (hscalar : ∀ i, Spec.map (CommRingCat.ofHom (v₀ i)) ≫ j i = a i ≫ q)
    (E : ∀ i, (Scheme.Modules.pullback (j i)).obj L ≅ SheafOfModules.unit (Spec (.of (M
      i))).ringCatSheaf)
    (F : ∀ i, (Scheme.Modules.pullback (a i)).obj
      ((Scheme.Modules.pullback q).obj L) ≅ SheafOfModules.unit (Spec (.of (A i))).ringCatSheaf)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    ∃ (R : Subalgebra ℤ K) (hSR : S ≤ R), start ≤ R ∧
      coframeAdjustmentStage S M A e v₀ q L j a hscalar E F R hSR := by
  obtain ⟨R₀, hSR₀, hstage⟩ := @exists_retained_coframe_adjustments.{u,v} K hK S I M A
      hMring hMalgebra hAring hAalgebra e v₀ Y YK q L j a hscalar E F hI hS hFlat hFP he
  let sr₀Algebra : Algebra S R₀ := (Subalgebra.inclusion hSR₀).toAlgebra
  let tower₀ : IsScalarTower S R₀ K := Subalgebra.inclusion.isScalarTower_right hSR₀ K
  change R₀.FG ∧ adjustedFamilyData (R := R₀) M A e v₀ q L j a hscalar E F at hstage
  obtain ⟨hR₀, d₀, hd₀, _, _⟩ := hstage
  let R : Subalgebra ℤ K := R₀ ⊔ start
  have hSR : S ≤ R := hSR₀.trans le_sup_left
  let srAlgebra : Algebra S R := (Subalgebra.inclusion hSR).toAlgebra
  let tower : IsScalarTower S R K := Subalgebra.inclusion.isScalarTower_right hSR K
  let f : R₀ →ₐ[S] R :=
    { __ := (Subalgebra.inclusion (show R₀ ≤ R from le_sup_left)).toRingHom
      commutes' := fun _ => rfl }
  have hf : (IsScalarTower.toAlgHom S R K).comp f = IsScalarTower.toAlgHom S R₀ K := by
    ext x
    rfl
  let d (i : I) : (R ⊗[S] M i)ˣ :=
    Units.map (Algebra.TensorProduct.map f (AlgHom.id S (M i))).toMonoidHom (d₀ i)
  let coefficientMap (i : I) : R ⊗[S] M i →+* A i :=
    @scalarMap S R K (M i) (A i)
      (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R))
      (inferInstanceAs (CommRing K)) (hMring i) (hAring i) srAlgebra
      (inferInstanceAs (Algebra S K)) (inferInstanceAs (Algebra R K))
      (hMalgebra i) (hAalgebra i) tower (e i)
  have hd (i : I) : coefficientMap i (d i : R ⊗[S] M i) =
      (affineCoframeUnit (A i)
        (FrobeniusSplitting.CharacterLine.squareFrameIso q (a i) (j i) (Spec.map (CommRingCat.ofHom
          (v₀ i)))
          (hscalar i) L (E i)) (F i) : A i) := by
    exact (@SchubertGeometry.DeterminantSection.scalar_extension
      S R₀ R K (M i) (A i)
      (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R₀))
      (inferInstanceAs (CommRing R)) (inferInstanceAs (CommRing K)) (hMring i) (hAring i)
      sr₀Algebra srAlgebra (inferInstanceAs (Algebra S K))
      (inferInstanceAs (Algebra R₀ K)) (inferInstanceAs (Algebra R K))
      tower₀ tower (hMalgebra i) (hAalgebra i) (e i) f hf
      (d₀ i : R₀ ⊗[S] M i)).trans (hd₀ i)
  refine ⟨R, hSR, le_sup_right, hR₀.sup hstart, ?_⟩
  refine @adjustments_of_units.{u,v} S R K
    (inferInstanceAs (CommRing S)) (inferInstanceAs (CommRing R))
    (inferInstanceAs (CommRing K)) srAlgebra (inferInstanceAs (Algebra S K))
    (inferInstanceAs (Algebra R K)) tower I M A hMring hMalgebra hAring hAalgebra
    e v₀ Y YK q L j a hscalar E F he d hd ?_
  intro i n
  exact (map_pow (coefficientMap i) (d i : R ⊗[S] M i) n).trans
    (congrArg (fun x : A i => x ^ n) (hd i))

variable {K : Type u} [hK : Field K] [hAlg : IsAlgClosed K] [hChar : CharZero K]
    (G : ReductiveGroupData K)
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
    (S : Subalgebra ℤ K)
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [hNopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hNdir : ((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
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

/-- The coframe units comparing the matching line with the opposition
preimage coframe are retained above any finite coefficient stage. -/
theorem exists_preimage_coframe_units (i : G.rootBase.support) (R : Subalgebra ℤ K) (hR : R.FG)
    {I : Type v} [Finite I] (M A : I → Type u)
    [∀ l, CommRing (M l)] [∀ l, Algebra R (M l)]
    [∀ l, Module.Flat R (M l)] [∀ l, Algebra.FinitePresentation R (M l)]
    [∀ l, CommRing (A l)] [∀ l, Algebra K (A l)]
    (e : ∀ l, K ⊗[R] M l ≃ₐ[K] A l)
    (j : ∀ l, Spec (.of (M l)) ⟶ cN.pt.left)
    (k : ∀ l, Spec (.of (A l)) ⟶ wordChartPreimage G word q i)
    (index : I → J)
    (small : ∀ l, Spec (.of (M l)) ⟶ Spec (.of (N.obj (singletonIndex (index l)))))
    (hsmall : ∀ l, j l = small l ≫ (cN.ι.app (op (singletonIndex (index l)))).left)
    (hscalar : ∀ l, Spec.map (CommRingCat.ofHom
      ((e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ j l =
        (k l ≫ SchubertGeometry.RetainedCharacter.preimageSnd G word q i) ≫ qN)
    (start : Subalgebra ℤ K) (hstart : start.FG) :
    let E := fun l => @frame_on_composite (Spec (.of (M l)))
      (Spec (.of (N.obj (singletonIndex (index l))))) cN.pt.left (small l)
      (cN.ι.app (op (singletonIndex (index l)))).left (j l) (hsmall l)
      (matchingModule N cN deltaN 1)
      (@localCharacterTrivialization S J (inferInstanceAs (CommRing S))
        N hNopen hNdir cN hcN deltaN 1 hcoN hnN
        (singletonIndex (index l)) (index l) (Finset.mem_singleton_self (index l)))
    let H := fun l => @frame_on_composite (Spec (.of (A l)))
      (wordChartPreimage G word q i) cF.pt.left (k l)
      (SchubertGeometry.RetainedCharacter.preimageSnd G word q i)
      (k l ≫ SchubertGeometry.RetainedCharacter.preimageSnd G word q i) rfl
      ((Scheme.Modules.pullback qN).obj (matchingModule N cN deltaN 1))
      (@wordChartPreimageFrame.{u} K hK hAlg hChar G J F hFopen hFdir
        cF hcF word q point a ha beta hgroup hco hn S (inferInstanceAs (CommRing S))
        N hNopen hNdir v deltaN hd cN hcN qN hqN hcoN hnN i 1)
    ∃ (T : Subalgebra ℤ K) (hRT : R ≤ T), start ≤ T ∧
      coframeAdjustmentStage R M A e
        (fun l => (e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
        qN (matchingModule N cN deltaN 1) j
        (fun l => k l ≫ SchubertGeometry.RetainedCharacter.preimageSnd G word q i)
        hscalar E H T hRT := by
  intro E H
  exact @retain_above.{u,v} K hK R hR I (inferInstanceAs (Finite I)) M A
    (inferInstanceAs (∀ l, CommRing (M l))) (inferInstanceAs (∀ l, Algebra R (M l)))
    (inferInstanceAs (∀ l, Module.Flat R (M l)))
    (inferInstanceAs (∀ l, Algebra.FinitePresentation R (M l)))
    (inferInstanceAs (∀ l, CommRing (A l))) (inferInstanceAs (∀ l, Algebra K (A l))) e
    (fun l => (e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
    (fun l x => rfl) cN.pt.left cF.pt.left qN (matchingModule N cN deltaN 1) j
    (fun l => k l ≫ SchubertGeometry.RetainedCharacter.preimageSnd G word q i)
    hscalar E H start hstart

end SchubertGeometry.RetainedCharacter
