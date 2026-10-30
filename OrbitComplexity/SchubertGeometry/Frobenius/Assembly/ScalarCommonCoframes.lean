import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RetainedPolynomialCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialCover
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCommonCover
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Coframes on the scalar common cover

The first cover is pulled back along the fixed scalar comparison. The
polynomial cover and both common-chart projections are constructed before
the retained units are used to glue the polynomial coframes.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open FrobeniusSplitting FrobeniusSplitting.CharacterLine
open FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct

open private affine_fibre_product from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameCoverRefinement
open private fieldMap oldMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialCover
open private adjustedFamilyData from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private compared_append_frame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits
open private wholeComparison comparedWholeFrame polynomialFineCoframe from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonPolynomialCoframes

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Fine and whole polynomial coframes for a prescribed family of field
charts, on the same line module and the same scalar cover. -/
def scalarPolynomialCoframeFamily {Y YK Z : Scheme.{u}}
    (n : YK ⟶ Y) (r : YK ⟶ Z) (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback n).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (W V : Y.OpenCover.{u}) {I : Type u} (index : V.I₀ → I)
    (P : I → Scheme.{u}) (g : ∀ i, P i ⟶ YK) (c : ∀ i, P i ⟶ Z)
    (hc : ∀ i, g i ≫ r = c i)
    (Epoly : ∀ i, (Scheme.Modules.pullback (c i)).obj LK ≅ unitModule (P i))
    (z : ∀ v, P (index v) ⟶ V.X v)
    (hwhole : ∀ v, z v ≫ V.f v = g (index v) ≫ n) : Prop :=
  ∀ v, ∃ E : ∀ w, (Scheme.Modules.pullback ((appendCommonCover W V).f ⟨w, v⟩)).obj L ≅
      unitModule ((commonPolynomialCover W V v).X w),
    polynomialCoframeComparison (z v) (commonPolynomialCover W V v)
      ((Scheme.Modules.pullback (V.f v)).obj L) (polynomialFineCoframe W V v L E)
      (wholeComparison n (V.f v) (g (index v)) (z v) (hwhole v) L ≪≫
        comparedWholeFrame r (g (index v)) (c (index v)) (hc (index v))
          ((Scheme.Modules.pullback n).obj L) LK EL (Epoly (index v)))

private theorem chart_codomain {A B C Y Z : Scheme.{u}}
    (E : C ≅ B) (p : A ⟶ B) (a : A ⟶ Y) (b : C ⟶ Z) (q : Y ⟶ Z)
    (h : IsPullback p a (E.inv ≫ b) q) : IsPullback (p ≫ E.inv) a b q := by
  exact h.of_iso (Iso.refl _) E.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- Construct the scalar polynomial cover and its whole coframes from the
retained units on the original common cover. -/
theorem exists_scalar_common_coframes {S T K : Type u}
    [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    (hT : Function.Injective (algebraMap T K))
    {Y YT YK Z : Scheme.{u}} [Y.IsSeparated] [YT.IsSeparated]
    (base : Y ⟶ Spec (.of S)) (baseT : YT ⟶ Spec (.of T)) [Smooth baseT]
    (baseK : YK ⟶ Spec (.of K)) (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T))))
    (hn : IsPullback n baseK baseT (Spec.map (CommRingCat.ofHom (algebraMap T K))))
    (hm : IsPullback m baseK base (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hbase : n ≫ q = m)
    (W V : Y.OpenCover.{u}) [Finite W.I₀] [Finite V.I₀]
    [∀ w, IsAffine (W.X w)] [∀ v, IsAffine (V.X v)]
    (A B : V.I₀ → Type u) [∀ v, CommRing (A v)] [∀ v, Algebra S (A v)]
    [hB : ∀ v, CommRing (B v)] [∀ v, Algebra K (B v)]
    (eV : ∀ v, V.X v ≅ Spec (.of (Polynomial (A v))))
    (hVbase : ∀ v, ((eV v).inv ≫ V.f v) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A v)))))
    (e₀ : ∀ v, K ⊗[S] A v ≃ₐ[K] B v)
    (jK : ∀ v, Spec (.of (Polynomial (B v))) ⟶ YK)
    (hjK : ∀ v, jK v ≫ m = Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom ((e₀ v).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom))) ≫ (eV v).inv ≫ V.f v)
    (hjKb : ∀ v, jK v ≫ baseK =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (B v)))))
    (r : YK ⟶ Z) (c : ∀ v, Spec (.of (Polynomial (B v))) ⟶ Z)
    (hc : ∀ v, jK v ≫ r = c v)
    (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback m).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (Epoly : ∀ v, (Scheme.Modules.pullback (c v)).obj LK ≅
      unitModule (Spec (.of (Polynomial (B v))))) :
    let C := appendCommonCover W V
    let : ∀ l : C.I₀, CommRing (B l.2) := fun l => hB l.2
    let : IsAffineHom m := MorphismProperty.of_isPullback hm.flip inferInstance
    let P := fun l : C.I₀ => pullback (C.f l) m
    let : ∀ l, Algebra S Γ(C.X l, ⊤) := fun l =>
      ((C.f l ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
    let : ∀ l, Algebra K Γ(P l, ⊤) := fun l =>
      ((pullback.snd (C.f l) m ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    let j := fun l : C.I₀ => (C.X l).isoSpec.inv ≫ C.f l
    let aQ := fun l : C.I₀ => (P l).isoSpec.inv ≫ pullback.snd (C.f l) m
    ∀ (e : ∀ l, K ⊗[S] Γ(C.X l, ⊤) ≃ₐ[K] Γ(P l, ⊤))
      (_he : ∀ l x, e l ((1 : K) ⊗ₜ[S] x) = (pullback.fst (C.f l) m).appTop.hom x)
      (kF : ∀ l : C.I₀, Spec Γ(P l, ⊤) ⟶ Spec (.of (Polynomial (B l.2))))
      (_hkF : ∀ l, kF l ≫ jK l.2 = aQ l)
      (hraw : ∀ l, aQ l ≫ r = kF l ≫ c l.2)
      (E : ∀ l, (Scheme.Modules.pullback (j l)).obj L ≅ unitModule (Spec Γ(C.X l, ⊤)))
      (hscalar : ∀ l, Spec.map (CommRingCat.ofHom
        ((e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ j l = aQ l ≫ m)
      (_hretain : adjustedFamilyData (R := T) (fun l => Γ(C.X l, ⊤)) (fun l => Γ(P l, ⊤)) e
        (fun l => (e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
        m L j aQ hscalar E
        (fun l => compared_append_frame m r (aQ l) L LK EL (kF l) (c l.2) (hraw l) (Epoly l.2))),
    let WT := W.pullback₂ q
    Finite WT.I₀ ∧
      ∃ (VT : YT.OpenCover.{u}) (_hfinite : Finite VT.I₀) (_haffine : ∀ v, IsAffine (VT.X v))
        (index : VT.I₀ ≃ V.I₀)
        (eVT : ∀ v, VT.X v ≅ Spec (.of (Polynomial (T ⊗[S] A (index v)))))
        (_hcart : ∀ v, IsPullback ((eVT v).hom ≫ oldMap) (VT.f v)
          ((eV (index v)).inv ≫ V.f (index v)) q)
        (_hstruct : ∀ v, VT.f v ≫ baseT = (eVT v).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap T (Polynomial (T ⊗[S] A (index v))))))
        (_hold : ∀ v, VT.f v ≫ q = (eVT v).hom ≫ oldMap ≫
          (eV (index v)).inv ≫ V.f (index v))
        (_hcoord : ∀ v, IsPullback (fieldMap (e₀ (index v))) (jK (index v))
          ((eVT v).inv ≫ VT.f v) n)
        (hactual : ∀ v, IsPullback (fieldMap (e₀ (index v)) ≫ (eVT v).inv)
          (jK (index v)) (VT.f v) n),
        (∀ v, jK (index v) ≫ n = fieldMap (e₀ (index v)) ≫ (eVT v).inv ≫ VT.f v) ∧
        scalarPolynomialCoframeFamily n r ((Scheme.Modules.pullback q).obj L) LK
          (((pullbackComp n q).app L ≪≫ (pullbackCongr hbase).app L) ≪≫ EL)
          WT VT index (fun v => Spec (.of (Polynomial (B v)))) jK c hc Epoly
          (fun v => fieldMap (e₀ (index v)) ≫ (eVT v).inv) (fun v => (hactual v).w) := by
  dsimp only
  let C := appendCommonCover W V
  let hCAffine : ∀ l : C.I₀, IsAffine (C.X l) := fun l => by
    let : IsAffine (W.X l.1) := (inferInstance : ∀ w, IsAffine (W.X w)) l.1
    let : IsAffine (V.X l.2) := (inferInstance : ∀ v, IsAffine (V.X v)) l.2
    exact affine_fibre_product (W.f l.1) (V.f l.2)
  let : IsAffineHom m := MorphismProperty.of_isPullback hm.flip inferInstance
  let : IsAffineHom q := MorphismProperty.of_isPullback hq.flip inferInstance
  let P := fun l : C.I₀ => pullback (C.f l) m
  let : ∀ l, Algebra S Γ(C.X l, ⊤) := fun l =>
    ((C.f l ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : ∀ l, Algebra K Γ(P l, ⊤) := fun l =>
    ((pullback.snd (C.f l) m ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let j := fun l : C.I₀ => (C.X l).isoSpec.inv ≫ C.f l
  let aQ := fun l : C.I₀ => (P l).isoSpec.inv ≫ pullback.snd (C.f l) m
  intro e he kF hkF hraw E hscalar hretain
  let WT := W.pullback₂ q
  let : Finite WT.I₀ := inferInstanceAs (Finite W.I₀)
  let : ∀ w, IsAffine (WT.X w) := fun w => by
    let : IsAffine (W.X w) := (inferInstance : ∀ w, IsAffine (W.X w)) w
    change IsAffine (pullback (W.f w) q)
    infer_instance
  obtain ⟨VT, hfinite, haffine, index, eVT, hcart, hstruct, hold, hcoord, hactual, hfield⟩ :=
    exists_scalar_polynomial_cover base baseT baseK q n m hq hn hm hbase V A eV hVbase B e₀ jK hjK
        hjKb
  let : Finite VT.I₀ := hfinite
  let : ∀ v, IsAffine (VT.X v) := haffine
  refine ⟨inferInstance, VT, hfinite, haffine, index, eVT, hcart, hstruct, hold,
    hcoord, hactual, hfield, ?_⟩
  intro v₀
  let : ∀ w : WT.I₀, IsAffine (C.X ⟨w, index v₀⟩) := fun w => hCAffine ⟨w, index v₀⟩
  let : ∀ w : WT.I₀, IsAffine (P ⟨w, index v₀⟩) := fun w => by
    change IsAffine (pullback (C.f ⟨w, index v₀⟩) m)
    infer_instance
  let : ∀ w : WT.I₀, Algebra S Γ(C.X ⟨w, index v₀⟩, ⊤) := fun w =>
    ((C.f ⟨w, index v₀⟩ ≫ base).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : ∀ w : WT.I₀, Algebra K Γ(P ⟨w, index v₀⟩, ⊤) := fun w =>
    ((pullback.snd (C.f ⟨w, index v₀⟩) m ≫ baseK).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let uW := fun w : WT.I₀ => pullback.fst (W.f w) q
  let uV := fun v : VT.I₀ => (eVT v).hom ≫ oldMap ≫ (eV (index v)).inv
  have hW (w : WT.I₀) : IsPullback (uW w) (WT.f w) (W.f w) q :=
    IsPullback.of_hasPullback (W.f w) q
  have hV (v : VT.I₀) : IsPullback (uV v) (VT.f v) (V.f (index v)) q :=
    chart_codomain (eV (index v)) ((eVT v).hom ≫ oldMap) (VT.f v) (V.f (index v)) q (hcart v)
  let model := fun w : WT.I₀ =>
    scalarCommonMap q W V WT VT (fun w => w) index uW uV
      (fun w => (hW w).w) (fun v => (hV v).w) ⟨w, v₀⟩
  have hC (w : WT.I₀) : IsPullback (model w)
      ((appendCommonCover WT VT).f ⟨w, v₀⟩) (C.f ⟨w, index v₀⟩) q :=
    scalarCommonMap_isPullback q W V WT VT (fun w => w) index uW uV
      (fun w => (hW w).w) (fun v => (hV v).w) hW hV ⟨w, v₀⟩
  have hretained : adjustedFamilyData (R := T)
      (fun w : WT.I₀ => Γ(C.X ⟨w, index v₀⟩, ⊤))
      (fun w : WT.I₀ => Γ(P ⟨w, index v₀⟩, ⊤))
      (fun w => e ⟨w, index v₀⟩)
      (fun w => (e ⟨w, index v₀⟩).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
      m L (fun w => j ⟨w, index v₀⟩) (fun w => aQ ⟨w, index v₀⟩)
      (fun w => hscalar ⟨w, index v₀⟩) (fun w => E ⟨w, index v₀⟩)
      (fun w => compared_append_frame m r (aQ ⟨w, index v₀⟩) L LK EL
        (kF ⟨w, index v₀⟩) (c (index v₀)) (hraw ⟨w, index v₀⟩) (Epoly (index v₀))) := by
    obtain ⟨d, hd, hpow, hcomp⟩ := hretain
    exact ⟨(fun w => d ⟨w, index v₀⟩), (fun w => hd ⟨w, index v₀⟩),
      (fun w t => hpow ⟨w, index v₀⟩ t), (fun w => hcomp ⟨w, index v₀⟩)⟩
  obtain ⟨_d, _hpow, ET, hET⟩ := exists_retained_polynomial_coframe hT base baseT baseK
    q n m hbase hq hn WT VT v₀ r (jK (index v₀))
    (fieldMap (e₀ (index v₀)) ≫ (eVT v₀).inv) (hactual v₀)
    (c (index v₀)) (hc (index v₀)) L LK EL (Epoly (index v₀))
    (fun w => C.X ⟨w, index v₀⟩) (fun w => P ⟨w, index v₀⟩)
    (fun w => C.f ⟨w, index v₀⟩) model hC
    (fun w => pullback.snd (C.f ⟨w, index v₀⟩) m)
    (fun w => pullback.fst (C.f ⟨w, index v₀⟩) m)
    (fun w => IsPullback.of_hasPullback (C.f ⟨w, index v₀⟩) m)
    (fun w => e ⟨w, index v₀⟩) (fun w => he ⟨w, index v₀⟩)
    (fun w => j ⟨w, index v₀⟩) (fun _ => rfl)
    (fun w => aQ ⟨w, index v₀⟩) (fun _ => rfl)
    (fun w => kF ⟨w, index v₀⟩) (fun w => hkF ⟨w, index v₀⟩)
    (fun w => hraw ⟨w, index v₀⟩) (fun w => E ⟨w, index v₀⟩)
    (fun w => hscalar ⟨w, index v₀⟩) hretained
  exact ⟨ET, hET⟩

end SchubertGeometry.RetainedCharacter
