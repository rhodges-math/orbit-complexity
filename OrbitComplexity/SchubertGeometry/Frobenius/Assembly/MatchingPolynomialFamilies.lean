import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCommonCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPolynomialCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedPolynomialFamilies
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCommonCover
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Matching polynomial coframes in every degree

One scalar model and one polynomial cover support the canonical matching
coframes in every character degree. Both are chosen before the degree.
-/

set_option autoImplicit false
noncomputable section
universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open ReductiveGroups GroupActions FrobeniusSplitting
open FrobeniusSplitting.CharacterLine FrobeniusSplitting.RetainedCharacter
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private polynomialData modelPolynomialData tensor_one from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPolynomialCoframes
open private fieldMap oldMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialCover
open private chart_codomain from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCommonCoframes
open private adjustedFamilyData from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private compared_append_frame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private affine_fibre_product from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameCoverRefinement
open private frame_on_composite from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private chartLift from
  OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.WordMatchingBase
open private stageFamilyData from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedCommonCoframes

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def polynomialFamilyData {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {Y YT YK Z : Scheme.{u}} (baseT : YT ⟶ Spec (.of T))
    (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y) (hbase : n ≫ q = m)
    (W V : Y.OpenCover.{u})
    (A : V.I₀ → CommAlgCat.{u} S) (B : V.I₀ → CommAlgCat.{u} K)
    (eV : ∀ z, V.X z ≅ Spec (.of (Polynomial (A z))))
    (e₀ : ∀ z, K ⊗[S] A z ≃ₐ[K] B z)
    (jK : ∀ z, Spec (.of (Polynomial (B z))) ⟶ YK)
    (r : YK ⟶ Z) (c : ∀ z, Spec (.of (Polynomial (B z))) ⟶ Z)
    (hc : ∀ z, jK z ≫ r = c z) (L : ℕ → Y.Modules) (LK : ℕ → Z.Modules)
    (EL : ∀ d, (Scheme.Modules.pullback m).obj (L d) ≅
      (Scheme.Modules.pullback r).obj (LK d))
    (Epoly : ∀ d z, (Scheme.Modules.pullback (c z)).obj (LK d) ≅
      unitModule (Spec (.of (Polynomial (B z))))) : Prop :=
  let WT := W.pullback₂ q
  Finite WT.I₀ ∧
    ∃ (VT : YT.OpenCover.{u}) (_hfinite : Finite VT.I₀) (_haffine : ∀ z, IsAffine (VT.X z))
      (index : VT.I₀ ≃ V.I₀)
      (eVT : ∀ z, VT.X z ≅ Spec (.of (Polynomial (T ⊗[S] A (index z)))))
      (_hcart : ∀ z, IsPullback ((eVT z).hom ≫ oldMap) (VT.f z)
        ((eV (index z)).inv ≫ V.f (index z)) q)
      (_hstruct : ∀ z, VT.f z ≫ baseT = (eVT z).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (T ⊗[S] A (index z))))))
      (_hold : ∀ z, VT.f z ≫ q = (eVT z).hom ≫ oldMap ≫
        (eV (index z)).inv ≫ V.f (index z))
      (_hcoord : ∀ z, IsPullback (fieldMap (e₀ (index z))) (jK (index z))
        ((eVT z).inv ≫ VT.f z) n)
      (hactual : ∀ z, IsPullback (fieldMap (e₀ (index z)) ≫ (eVT z).inv)
        (jK (index z)) (VT.f z) n),
      (∀ z, jK (index z) ≫ n = fieldMap (e₀ (index z)) ≫ (eVT z).inv ≫ VT.f z) ∧
      ∀ d, scalarPolynomialCoframeFamily n r ((Scheme.Modules.pullback q).obj (L d)) (LK d)
        (((pullbackComp n q).app (L d) ≪≫ (pullbackCongr hbase).app (L d)) ≪≫ EL d)
        WT VT index (fun z => Spec (.of (Polynomial (B z)))) jK c hc (Epoly d)
        (fun z => fieldMap (e₀ (index z)) ≫ (eVT z).inv) (fun z => (hactual z).w)

private def modelPolynomialFamilyData {J : Type v} [Category.{w} J]
    {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    (N : J ⥤ CommAlgCat.{u} S) (cN : Cocone (N.op ⋙ algSpec (.of S)))
    {YK Z : Scheme.{u}} (baseK : YK ⟶ Spec (.of K)) (m : YK ⟶ cN.pt.left)
    (W V : cN.pt.left.OpenCover.{u})
    (A : V.I₀ → CommAlgCat.{u} S) (B : V.I₀ → CommAlgCat.{u} K)
    (eV : ∀ z, V.X z ≅ Spec (.of (Polynomial (A z))))
    (e₀ : ∀ z, K ⊗[S] A z ≃ₐ[K] B z)
    (jK : ∀ z, Spec (.of (Polynomial (B z))) ⟶ YK)
    (r : YK ⟶ Z) (c : ∀ z, Spec (.of (Polynomial (B z))) ⟶ Z)
    (hc : ∀ z, jK z ≫ r = c z) (L : ℕ → cN.pt.left.Modules) (LK : ℕ → Z.Modules)
    (EL : ∀ d, (Scheme.Modules.pullback m).obj (L d) ≅
      (Scheme.Modules.pullback r).obj (LK d))
    (Epoly : ∀ d z, (Scheme.Modules.pullback (c z)).obj (LK d) ≅
      unitModule (Spec (.of (Polynomial (B z))))) : Prop :=
  let NT := fixedFibreDiagram (R := T) (M := T) N
  (∀ {i j : Jᵒᵖ} (f : i ⟶ j),
    IsOpenImmersion (((NT.op ⋙ algSpec (.of T)).map f).left)) ∧
    ((((NT.op ⋙ algSpec (.of T)) ⋙ Over.forget (Spec (.of T))) ⋙
      Scheme.forget).IsLocallyDirected) ∧
    ∃ (cT : Cocone (NT.op ⋙ algSpec (.of T))) (q : cT.pt.left ⟶ cN.pt.left)
      (n : YK ⟶ cT.pt.left) (_hcT : IsColimit cT)
      (_hq : IsPullback q cT.pt.hom cN.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap S T))))
      (_hn : IsPullback n baseK cT.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap T K))))
      (hbase : n ≫ q = m),
      (n ≫ cT.pt.hom = baseK ≫ Spec.map (CommRingCat.ofHom (algebraMap T K))) ∧
      (∀ i, (cT.ι.app i).left ≫ q = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : N.obj i.unop →ₐ[S]
          T ⊗[S] N.obj i.unop).toRingHom) ≫ (cN.ι.app i).left) ∧
      Smooth cT.pt.hom ∧ cT.pt.left.IsSeparated ∧
      polynomialFamilyData cT.pt.hom q n m hbase W V A B eV e₀ jK r c hc L LK EL Epoly

private theorem adjusted_reindex {S T K : Type u}
    [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {I H : Type u} (σ : H → I) (M A : I → Type u)
    [∀ z, CommRing (M z)] [algM : ∀ z, Algebra S (M z)]
    [∀ z, CommRing (A z)] [algA : ∀ z, Algebra K (A z)]
    (e : ∀ z, K ⊗[S] M z ≃ₐ[K] A z) (v₀ : ∀ z, M z →+* A z)
    {Y YK : Scheme.{u}} (q : YK ⟶ Y) (L : Y.Modules)
    (j : ∀ z, Spec (.of (M z)) ⟶ Y) (a : ∀ z, Spec (.of (A z)) ⟶ YK)
    (hs : ∀ z, Spec.map (CommRingCat.ofHom (v₀ z)) ≫ j z = a z ≫ q)
    (E : ∀ z, (Scheme.Modules.pullback (j z)).obj L ≅ unitModule (Spec (.of (M z))))
    (F : ∀ z, (Scheme.Modules.pullback (a z)).obj ((Scheme.Modules.pullback q).obj L) ≅
      unitModule (Spec (.of (A z))))
    (h : adjustedFamilyData (R := T) M A e v₀ q L j a hs E F) :
    adjustedFamilyData (R := T) (fun z => M (σ z)) (fun z => A (σ z))
      (fun z => e (σ z)) (fun z => v₀ (σ z)) q L (fun z => j (σ z)) (fun z => a (σ z))
      (fun z => hs (σ z)) (fun z => E (σ z)) (fun z => F (σ z)) := by
  obtain ⟨d, hd, hpow, hframe⟩ := h
  exact ⟨fun z => d (σ z), fun z => hd (σ z), fun z n => hpow (σ z) n,
    fun z => hframe (σ z)⟩

section Fixed

variable {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    (hT : Function.Injective (algebraMap T K))
    {Y YT YK Z : Scheme.{u}} [YT.IsSeparated]
    (base : Y ⟶ Spec (.of S)) (baseT : YT ⟶ Spec (.of T)) [Smooth baseT]
    (baseK : YK ⟶ Spec (.of K)) (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y)
    (hbase : n ≫ q = m)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hn : IsPullback n baseK baseT (Spec.map (CommRingCat.ofHom (algebraMap T K))))
    (W V : Y.OpenCover.{u}) [hWaffine : ∀ z, IsAffine (W.X z)]
    (A : V.I₀ → CommAlgCat.{u} S) (B : V.I₀ → CommAlgCat.{u} K)
    (eV : ∀ z, V.X z ≅ Spec (.of (Polynomial (A z))))
    (e₀ : ∀ z, K ⊗[S] A z ≃ₐ[K] B z)
    (jK : ∀ z, Spec (.of (Polynomial (B z))) ⟶ YK)
    (r : YK ⟶ Z) (c : ∀ z, Spec (.of (Polynomial (B z))) ⟶ Z)
    (hc : ∀ z, jK z ≫ r = c z) (L : ℕ → Y.Modules) (LK : ℕ → Z.Modules)
    (EL : ∀ d, (Scheme.Modules.pullback m).obj (L d) ≅
      (Scheme.Modules.pullback r).obj (LK d))
    (Epoly : ∀ d z, (Scheme.Modules.pullback (c z)).obj (LK d) ≅
      unitModule (Spec (.of (Polynomial (B z)))))
    [hColdAffine : ∀ l, IsAffine ((appendCommonCover W V).X l)]
    (P : (appendCommonCover W V).I₀ → Scheme.{u}) [hPaffine : ∀ l, IsAffine (P l)]
    (p : ∀ l, P l ⟶ (appendCommonCover W V).X l) (a : ∀ l, P l ⟶ YK)
    (hP : ∀ l, IsPullback (p l) (a l) ((appendCommonCover W V).f l) m)

include hT hq hn hP hWaffine hColdAffine hPaffine in
private theorem fixed_families :
    let C := appendCommonCover W V
    let : ∀ l, Algebra S Γ(C.X l, ⊤) := fun l =>
      ((C.f l ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let : ∀ l, Algebra K Γ(P l, ⊤) := fun l =>
      ((a l ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    ∀ (e : ∀ l, K ⊗[S] Γ(C.X l, ⊤) ≃ₐ[K] Γ(P l, ⊤))
      (_he : ∀ l x, e l ((1 : K) ⊗ₜ[S] x) = (p l).appTop.hom x)
      (j : ∀ l, Spec Γ(C.X l, ⊤) ⟶ Y)
      (_hj : ∀ l, (C.X l).isoSpec.inv ≫ C.f l = j l)
      (aQ : ∀ l, Spec Γ(P l, ⊤) ⟶ YK)
      (_haQ : ∀ l, (P l).isoSpec.inv ≫ a l = aQ l)
      (kF : ∀ l, Spec Γ(P l, ⊤) ⟶ Spec (.of (Polynomial (B l.2))))
      (_hkF : ∀ l, kF l ≫ jK l.2 = aQ l)
      (hraw : ∀ l, aQ l ≫ r = kF l ≫ c l.2)
      (E : ∀ d l, (Scheme.Modules.pullback (j l)).obj (L d) ≅
        unitModule (Spec Γ(C.X l, ⊤)))
      (hscalar : ∀ l, Spec.map (CommRingCat.ofHom
        ((e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ j l = aQ l ≫ m)
      (_hretain : ∀ d, adjustedFamilyData (R := T)
        (fun l => Γ(C.X l, ⊤)) (fun l => Γ(P l, ⊤)) e
        (fun l => (e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
        m (L d) j aQ hscalar (E d)
        (fun l => compared_append_frame m r (aQ l) (L d) (LK d) (EL d)
          (kF l) (c l.2) (hraw l) (Epoly d l.2))),
    polynomialData baseT q n m hbase W V A B eV e₀ jK r c hc
      (L 1) (LK 1) (EL 1) (Epoly 1) →
    polynomialFamilyData baseT q n m hbase W V A B eV e₀ jK r c hc L LK EL Epoly := by
  intro C algC algP e he j hj aQ haQ kF hkF hraw E hscalar hretain hdata
  let (l : C.I₀) : Algebra S Γ(C.X l, ⊤) := algC l
  let (l : C.I₀) : Algebra K Γ(P l, ⊤) := algP l
  obtain ⟨hfinite, VT, hVTfinite, hVTaffine, index, eVT, hcart, hstruct, hold,
    hcoord, hactual, hfield, _hdegree⟩ := hdata
  let WT := W.pullback₂ q
  let : IsAffineHom q := MorphismProperty.of_isPullback hq.flip inferInstance
  let u (z : WT.I₀) : WT.X z ⟶ W.X z := pullback.fst (W.f z) q
  have hu (z : WT.I₀) : u z ≫ W.f z = WT.f z ≫ q := pullback.condition
  have hU (z : WT.I₀) : IsPullback (u z) (WT.f z) (W.f z) q := .of_hasPullback _ _
  let v₀ (z : VT.I₀) : VT.X z ⟶ V.X (index z) :=
    (eVT z).hom ≫ oldMap ≫ (eV (index z)).inv
  have hV (z : VT.I₀) : IsPullback (v₀ z) (VT.f z) (V.f (index z)) q :=
    chart_codomain (eV (index z)) _ _ _ _ (hcart z)
  have hv (z : VT.I₀) : v₀ z ≫ V.f (index z) = VT.f z ≫ q := (hV z).w
  let model (z : VT.I₀) (w : WT.I₀) :=
    scalarCommonMap q W V WT VT (fun w => w) index u v₀ hu hv ⟨w, z⟩
  have hC (z : VT.I₀) (w : WT.I₀) : IsPullback (model z w)
      ((appendCommonCover WT VT).f ⟨w, z⟩) (C.f ⟨w, index z⟩) q :=
    scalarCommonMap_isPullback q W V WT VT (fun w => w) index u v₀ hu hv hU hV ⟨w, z⟩
  let v₁ (l : C.I₀) : Γ(C.X l, ⊤) →+* Γ(P l, ⊤) :=
    (e l).toRingHom.comp
      (Algebra.TensorProduct.includeRight : Γ(C.X l, ⊤) →ₐ[S] K ⊗[S] Γ(C.X l, ⊤)).toRingHom
  have retain (d : ℕ) (z : VT.I₀) := adjusted_reindex (S := S) (T := T) (K := K)
    (algM := algC) (algA := algP)
    (fun w : WT.I₀ => (⟨w, index z⟩ : C.I₀))
    (fun l => Γ(C.X l, ⊤)) (fun l => Γ(P l, ⊤)) e
    v₁
    m (L d) j aQ hscalar (E d)
    (fun l => compared_append_frame m r (aQ l) (L d) (LK d) (EL d)
      (kF l) (c l.2) (hraw l) (Epoly d l.2)) (hretain d)
  have family := @retainedPolynomialCoframe_family S T K _ _ _ _ _ _ _ hT
    Y YT YK Z inferInstance base baseT inferInstance baseK q n m hbase hq hn
    WT VT (fun z => by
      let : IsAffine (W.X z) := hWaffine z
      exact inferInstanceAs (IsAffine (pullback (W.f z) q))) hVTaffine
    (fun z => Spec (.of (Polynomial (B (index z))))) r
    (fun z => jK (index z)) (fun z => fieldMap (e₀ (index z)) ≫ (eVT z).inv) hactual
    (fun z => c (index z)) (fun z => hc (index z)) L LK EL
    (fun d z => Epoly d (index z))
    (fun z w => C.X ⟨w, index z⟩) (fun z w => P ⟨w, index z⟩)
    (fun z w => hColdAffine ⟨w, index z⟩) (fun z w => hPaffine ⟨w, index z⟩)
    (fun z w => C.f ⟨w, index z⟩) model hC
    (fun z w => a ⟨w, index z⟩) (fun z w => p ⟨w, index z⟩)
    (fun z w => hP ⟨w, index z⟩)
    (fun z w => e ⟨w, index z⟩) (fun z w => he ⟨w, index z⟩)
    (fun z w => j ⟨w, index z⟩) (fun z w => hj ⟨w, index z⟩)
    (fun z w => aQ ⟨w, index z⟩) (fun z w => haQ ⟨w, index z⟩)
    (fun z w => kF ⟨w, index z⟩) (fun z w => hkF ⟨w, index z⟩)
    (fun z w => hraw ⟨w, index z⟩) (fun d z w => E d ⟨w, index z⟩)
    (fun z w => hscalar ⟨w, index z⟩) retain
  refine ⟨hfinite, VT, hVTfinite, hVTaffine, index, eVT, hcart, hstruct, hold,
    hcoord, hactual, hfield, ?_⟩
  exact fun d z => family d z

end Fixed

private theorem model_family {J : Type v} [Category.{w} J]
    {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    (N : J ⥤ CommAlgCat.{u} S) (cN : Cocone (N.op ⋙ algSpec (.of S)))
    {YK Z : Scheme.{u}} (baseK : YK ⟶ Spec (.of K)) (m : YK ⟶ cN.pt.left)
    (W V : cN.pt.left.OpenCover.{u})
    (A : V.I₀ → CommAlgCat.{u} S) (B : V.I₀ → CommAlgCat.{u} K)
    (eV : ∀ z, V.X z ≅ Spec (.of (Polynomial (A z))))
    (e₀ : ∀ z, K ⊗[S] A z ≃ₐ[K] B z)
    (jK : ∀ z, Spec (.of (Polynomial (B z))) ⟶ YK)
    (r : YK ⟶ Z) (c : ∀ z, Spec (.of (Polynomial (B z))) ⟶ Z)
    (hc : ∀ z, jK z ≫ r = c z) (L : ℕ → cN.pt.left.Modules) (LK : ℕ → Z.Modules)
    (EL : ∀ d, (Scheme.Modules.pullback m).obj (L d) ≅
      (Scheme.Modules.pullback r).obj (LK d))
    (Epoly : ∀ d z, (Scheme.Modules.pullback (c z)).obj (LK d) ≅
      unitModule (Spec (.of (Polynomial (B z)))))
    (hdata : modelPolynomialData (T := T) N cN baseK m W V A B eV e₀ jK r c hc
      (L 1) (LK 1) (EL 1) (Epoly 1))
    (extend : ∀ {YT : Scheme.{u}} (baseT : YT ⟶ Spec (.of T))
      (q : YT ⟶ cN.pt.left) (n : YK ⟶ YT)
      (_hq : IsPullback q baseT cN.pt.hom
        (Spec.map (CommRingCat.ofHom (algebraMap S T))))
      (_hn : IsPullback n baseK baseT (Spec.map (CommRingCat.ofHom (algebraMap T K))))
      (hbase : n ≫ q = m), Smooth baseT → YT.IsSeparated →
      polynomialData baseT q n m hbase W V A B eV e₀ jK r c hc
        (L 1) (LK 1) (EL 1) (Epoly 1) →
      polynomialFamilyData baseT q n m hbase W V A B eV e₀ jK r c hc L LK EL Epoly) :
    modelPolynomialFamilyData (T := T) N cN baseK m W V A B eV e₀ jK r c hc L LK EL Epoly := by
  obtain ⟨hopen, hdir, cT, q, n, hcT, hq, hn, hbase, hnbase, hlegs,
    hsmooth, hsep, hpoly⟩ := hdata
  exact ⟨hopen, hdir, cT, q, n, hcT, hq, hn, hbase, hnbase, hlegs, hsmooth, hsep,
    extend cT.pt.hom q n hq hn hbase hsmooth hsep hpoly⟩


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

variable [Finite J] [cN.pt.left.IsSeparated] [Smooth cN.pt.hom]
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

variable
    (hV : ∀ z, IsPullback (π z) (jK z) (V.f z) qN)
    (hword : ∀ z, jK z ≫ q = projectiveLinePolynomialChart (B z) (ε z) ≫
      projectiveAppendChart G i (B z) (p z) (c z))
    (T : Subalgebra ℤ K) (hST : S ≤ T)
    (A₀ : V.I₀ → CommAlgCat.{u} S)
    (eV : ∀ z, V.X z ≅ Spec (.of (Polynomial (A₀ z))))
    (hVbase : ∀ z, ((eV z).inv ≫ V.f z) ≫ cN.pt.hom =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A₀ z)))))
    (e₀ : ∀ z, K ⊗[S] A₀ z ≃ₐ[K] B z)
    (hπ : ∀ z, π z = Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom ((e₀ z).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom))) ≫ (eV z).inv)
    (hjKb : ∀ z, jK z ≫ cF.pt.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (B z)))))

include hV hword hπ hVbase hjKb in
/-- The canonical common-chart family gives every character degree on one
scalar matching model and one polynomial cover, preserving their projections. -/
theorem exists_matching_polynomial_families
    (eNodes : ∀ s, K ⊗[S] N.obj s ≃ₐ[K] F.obj s)
    (heNodes : ∀ s x, eNodes s ((1 : K) ⊗ₜ[S] x) = (v.app s).hom x)
    (hqBase : q ≫ bsdhToSpec G (word ++ [i]) = cF.pt.hom)
    (hdata : commonMatchingCoframeData G word i S N cN hcN deltaN hcoN hnN
      cF.pt.hom qN hK q
      (retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN 1)
      V V₀ g a₀ c hend B p ε π jK T hST) :
    let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
    let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
    modelPolynomialFamilyData (T := T) N cN cF.pt.hom qN
      (matchingSingletonCover N cN hcN) V A₀ B eV e₀ jK q
      (fun z => projectiveLinePolynomialChart (B z) (ε z) ≫
        projectiveAppendChart G i (B z) (p z) (c z)) hword
      (fun d => matchingModule N cN deltaN d)
      (fun d => CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ d) (word ++ [i]))
      (fun d => retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta hgroup hco hn
        N v deltaN hd cN hcN qN hqN hcoN hnN d)
      (fun d z => appendPolynomialFrame G word i (V₀ z) (g z) (a₀ z) (c z) (hend z)
        (B z) (p z) d (ε z)) := by
  classical
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let L := fun d => matchingModule N cN deltaN d
  let LK := fun d => CharacterLine.wordCharacterModule G
    (G.positiveRootCharacter ^ d) (word ++ [i])
  let EL := fun d => retainedWordLineIso G F cF hcF (word ++ [i]) q point a ha beta
    hgroup hco hn N v deltaN hd cN hcN qN hqN hcoN hnN d
  let Epoly := fun d z => appendPolynomialFrame G word i (V₀ z) (g z) (a₀ z)
    (c z) (hend z) (B z) (p z) d (ε z)
  let polyLeg := fun z => projectiveLinePolynomialChart (B z) (ε z) ≫
    projectiveAppendChart G i (B z) (p z) (c z)
  have hOld := exists_matching_polynomial_coframes G word i S N cN hcN deltaN hcoN hnN
    cF.pt.hom qN hK q (EL 1) V V₀ g a₀ c hend B p ε π jK hV hword
    T hST A₀ eV hVbase e₀ hπ hjKb hdata
  have hCommon := commonMatchingCoframe_families G F cF hcF word i q point a ha beta
    hgroup hco hn S N v deltaN hd cN hcN qN hqN hcoN hnN hK V V₀ g a₀ c hend B p ε π jK
    eNodes heNodes hqBase T hST hdata
  let W := matchingSingletonCover N cN hcN
  let C := appendCommonCover W V
  let : Finite W.I₀ := inferInstanceAs (Finite J)
  let : ∀ z, IsAffine (W.X z) := fun z =>
    inferInstanceAs (IsAffine (Spec (.of (N.obj (singletonIndex z)))))
  let : ∀ l, IsAffine (C.X l) := fun l => by
    let : IsAffine (W.X l.1) := inferInstance
    let : IsAffine (V.X l.2) := (inferInstance : ∀ z, IsAffine (V.X z)) l.2
    exact affine_fibre_product (W.f l.1) (V.f l.2)
  let : IsAffineHom qN := MorphismProperty.of_isPullback hK.flip inferInstance
  let P := fun l : C.I₀ => pullback (C.f l) qN
  let : ∀ l, IsAffine (P l) := fun _ => inferInstance
  let M : C.I₀ → Type u := fun l => Γ(C.X l, ⊤)
  let A : C.I₀ → Type u := fun l => Γ(P l, ⊤)
  let : ∀ l, Algebra S (M l) := fun l =>
    ((C.f l ≫ cN.pt.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : ∀ l, Algebra K (A l) := fun l =>
    ((pullback.snd (C.f l) qN ≫ cF.pt.hom).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let j := fun l : C.I₀ => (C.X l).isoSpec.inv ≫ C.f l
  let jF := fun l : C.I₀ => (P l).isoSpec.inv ≫ pullback.snd (C.f l) qN
  obtain ⟨small, _kN, kF, e, hscalar, hsmall, hk,
    _hkn, _hcross, hkf, he, _hFlat, _hFP, hFamily⟩ := hCommon
  obtain ⟨_hFG, _d, _hImages, hretain⟩ := hFamily
  let E := fun d l => frame_on_composite (small l)
    (cN.ι.app (op (singletonIndex l.1))).left (j l) (hsmall l) (L d)
    (localCharacterTrivialization N cN hcN deltaN d hcoN hnN
      (singletonIndex l.1) l.1 (Finset.mem_singleton_self l.1))
  apply model_family N cN cF.pt.hom qN W V A₀ B eV e₀ jK q polyLeg hword L LK EL Epoly hOld
  intro YT baseT qT n hqT hn hnq hsmooth hsep hpoly
  let : Smooth baseT := hsmooth
  let : YT.IsSeparated := hsep
  exact fixed_families (show Function.Injective (algebraMap T K) from Subtype.val_injective)
    cN.pt.hom baseT cF.pt.hom qT n qN hnq hqT hn W V A₀ B eV e₀ jK
    q polyLeg hword L LK EL Epoly P
    (fun l => pullback.fst (C.f l) qN) (fun l => pullback.snd (C.f l) qN)
    (fun l => IsPullback.of_hasPullback (C.f l) qN)
    e (fun l => tensor_one (e l) (pullback.fst (C.f l) qN).appTop.hom (he l))
    j (fun _ => rfl) jF (fun _ => rfl) kF hkf hk E hscalar hretain hpoly

end SchubertGeometry.RetainedCharacter
