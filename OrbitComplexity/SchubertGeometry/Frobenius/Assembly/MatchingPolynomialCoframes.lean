import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.CommonMatchingCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarCommonCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.FixedScalarComparison
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Whole polynomial coframes on the retained matching model

The prescribed matching model is scalar-extended over the coefficient
stage that already retains its coframe units. Its polynomial coframes and
field comparisons are constructed on that same scalar model.
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

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private matchingRefinementFrame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingAppendCoframes
open private affine_fibre_product from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameCoverRefinement
open private fieldMap oldMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.ScalarPolynomialCover
open private adjustedFamilyData from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.RetainedCoframeAdjustments
open private append_frame from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.RefinedAppendUnits

namespace SchubertGeometry.RetainedCharacter

private abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

private def polynomialData {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {Y YT YK Z : Scheme.{u}} (baseT : YT ⟶ Spec (.of T))
    (q : YT ⟶ Y) (n : YK ⟶ YT) (m : YK ⟶ Y) (hbase : n ≫ q = m)
    (W V : Y.OpenCover.{u})
    (A : V.I₀ → CommAlgCat.{u} S) (B : V.I₀ → CommAlgCat.{u} K)
    (eV : ∀ v, V.X v ≅ Spec (.of (Polynomial (A v))))
    (e₀ : ∀ v, K ⊗[S] A v ≃ₐ[K] B v)
    (jK : ∀ v, Spec (.of (Polynomial (B v))) ⟶ YK)
    (r : YK ⟶ Z) (c : ∀ v, Spec (.of (Polynomial (B v))) ⟶ Z)
    (hc : ∀ v, jK v ≫ r = c v) (L : Y.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback m).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (Epoly : ∀ v, (Scheme.Modules.pullback (c v)).obj LK ≅
      unitModule (Spec (.of (Polynomial (B v))))) : Prop :=
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
        (fun v => fieldMap (e₀ (index v)) ≫ (eVT v).inv) (fun v => (hactual v).w)

private def modelPolynomialData {J : Type v} [Category.{w} J]
    {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    (N : J ⥤ CommAlgCat.{u} S) (cN : Cocone (N.op ⋙ algSpec (.of S)))
    {YK Z : Scheme.{u}} (baseK : YK ⟶ Spec (.of K)) (m : YK ⟶ cN.pt.left)
    (W V : cN.pt.left.OpenCover.{u})
    (A : V.I₀ → CommAlgCat.{u} S) (B : V.I₀ → CommAlgCat.{u} K)
    (eV : ∀ v, V.X v ≅ Spec (.of (Polynomial (A v))))
    (e₀ : ∀ v, K ⊗[S] A v ≃ₐ[K] B v)
    (jK : ∀ v, Spec (.of (Polynomial (B v))) ⟶ YK)
    (r : YK ⟶ Z) (c : ∀ v, Spec (.of (Polynomial (B v))) ⟶ Z)
    (hc : ∀ v, jK v ≫ r = c v) (L : cN.pt.left.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback m).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (Epoly : ∀ v, (Scheme.Modules.pullback (c v)).obj LK ≅
      unitModule (Spec (.of (Polynomial (B v))))) : Prop :=
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
      polynomialData cT.pt.hom q n m hbase W V A B eV e₀ jK r c hc L LK EL Epoly

private theorem scalar_properties {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {Y YT : Scheme.{u}} [Y.IsSeparated]
    (base : Y ⟶ Spec (.of S)) [Smooth base] (baseT : YT ⟶ Spec (.of T)) (q : YT ⟶ Y)
    (hq : IsPullback q baseT base (Spec.map (CommRingCat.ofHom (algebraMap S T)))) :
    Smooth baseT ∧ YT.IsSeparated := by
  let : Smooth baseT := MorphismProperty.of_isPullback hq inferInstance
  let : IsSeparated baseT := MorphismProperty.of_isPullback hq inferInstance
  refine ⟨inferInstance, ⟨?_⟩⟩
  have h : IsSeparated (baseT ≫ terminal.from (Spec (.of T))) := inferInstance
  simpa only [terminal.comp_from] using h

private theorem extend_model_frames {J : Type v} [Category.{w} J] [Quiver.IsThin J] [Small.{u} J]
    {S T K : Type u} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    (N : J ⥤ CommAlgCat.{u} S)
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsOpenImmersion (((N.op ⋙ algSpec (.of S)).map f).left)]
    [(((N.op ⋙ algSpec (.of S)) ⋙ Over.forget (Spec (.of S))) ⋙ Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of S))) (hcN : IsColimit cN)
    [cN.pt.left.IsSeparated] [Smooth cN.pt.hom]
    {YK Z : Scheme.{u}} (baseK : YK ⟶ Spec (.of K)) (m : YK ⟶ cN.pt.left)
    (hm : IsPullback m baseK cN.pt.hom (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (W V : cN.pt.left.OpenCover.{u})
    (A : V.I₀ → CommAlgCat.{u} S) (B : V.I₀ → CommAlgCat.{u} K)
    (eV : ∀ v, V.X v ≅ Spec (.of (Polynomial (A v))))
    (e₀ : ∀ v, K ⊗[S] A v ≃ₐ[K] B v)
    (jK : ∀ v, Spec (.of (Polynomial (B v))) ⟶ YK)
    (r : YK ⟶ Z) (c : ∀ v, Spec (.of (Polynomial (B v))) ⟶ Z)
    (hc : ∀ v, jK v ≫ r = c v) (L : cN.pt.left.Modules) (LK : Z.Modules)
    (EL : (Scheme.Modules.pullback m).obj L ≅ (Scheme.Modules.pullback r).obj LK)
    (Epoly : ∀ v, (Scheme.Modules.pullback (c v)).obj LK ≅ unitModule (Spec (.of (Polynomial (B
        v)))))
    (frames : ∀ {YT : Scheme.{u}} (baseT : YT ⟶ Spec (.of T)) (q : YT ⟶ cN.pt.left)
      (n : YK ⟶ YT)
      (_hq : IsPullback q baseT cN.pt.hom (Spec.map (CommRingCat.ofHom (algebraMap S T))))
      (_hn : IsPullback n baseK baseT (Spec.map (CommRingCat.ofHom (algebraMap T K))))
      (hbase : n ≫ q = m), Smooth baseT → YT.IsSeparated →
        polynomialData baseT q n m hbase W V A B eV e₀ jK r c hc L LK EL Epoly) :
    modelPolynomialData (T := T) N cN baseK m W V A B eV e₀ jK r c hc L LK EL Epoly := by
  obtain ⟨ho, hd, cT, q, n, hcT, hq, hn, hbase, hnb, hlegs⟩ :=
    exists_fixed_scalar_comparison (T := T) N cN hcN baseK m hm
  obtain ⟨hsmooth, hseparated⟩ := scalar_properties cN.pt.hom cT.pt.hom q hq
  exact ⟨ho, hd, cT, q, n, hcT.some, hq, hn, hbase, hnb, hlegs, hsmooth, hseparated,
    frames cT.pt.hom q n hq hn hbase hsmooth hseparated⟩

private theorem tensor_one {S K M A : Type u} [CommRing S] [CommRing K]
    [CommRing M] [CommRing A] [Algebra S K] [Algebra S M] [Algebra K A]
    (e : K ⊗[S] M ≃ₐ[K] A) (v : M →+* A)
    (h : ∀ k x, e (k ⊗ₜ[S] x) = algebraMap K A k * v x) (x : M) :
    e ((1 : K) ⊗ₜ[S] x) = v x :=
  (h 1 x).trans (by rw [map_one, one_mul])

private theorem polynomial_projection {C : Type u} [Category C] {A B X Y : C}
    (pi : A ⟶ B) (j : A ⟶ X) (f : B ⟶ Y) (m : X ⟶ Y)
    (k : A ⟶ B) (hpi : pi = k) (h : pi ≫ f = j ≫ m) : j ≫ m = k ≫ f :=
  h.symm.trans (congrArg (fun t => t ≫ f) hpi)

section Matching

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroupData K) (word : List G.rootBase.support) (i : G.rootBase.support)
    (S : Subalgebra ℤ K) {J : Type u} [Finite J]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of S))) (hcN : IsColimit cN)
    [cN.pt.left.IsSeparated] [Smooth cN.pt.hom]
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))
    {YK : Scheme.{u}} (baseK : YK ⟶ Spec (.of K)) (q : YK ⟶ cN.pt.left)
    (hK : IsPullback q baseK cN.pt.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (r : YK ⟶ bsdhScheme G (word ++ [i]))
    (EL : (Scheme.Modules.pullback q).obj
        (FrobeniusSplitting.RetainedCharacter.matchingModule N cN delta 1) ≅
      (Scheme.Modules.pullback r).obj
        (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) (word ++ [i])))
    (V : cN.pt.left.OpenCover.{u}) [Finite V.I₀] [∀ v, IsAffine (V.X v)]
    (V₀ : V.I₀ → Over (Spec (.of K))) (g : V.I₀ → G.points)
    (a₀ : ∀ v, V₀ v ⟶ (oppositeUnipotentVariety G).toOver)
    (c : ∀ v, V₀ v ⊗ (schubertVariety G
      (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver ⟶
        Over.mk (bsdhToSpec G (word ++ [i])))
    (hend : ∀ v, (c v).left ≫ (bsdhAppendIso G word i).hom.left ≫
      pullback.snd (bsdhMap G word) (flagBundleProjection G
        (schubertVariety G (RootPairing.weylGroup.ofIdx G.rootSystem i.val))) =
      (a₀ v ⊗ₘ 𝟙 (schubertVariety G
        (RootPairing.weylGroup.ofIdx G.rootSystem i.val)).toOver).left ≫ flagBundleChart G _ (g v))
    (B : V.I₀ → CommAlgCat.{u} K)
    (p : ∀ v, (algSpec (.of K)).obj (op (B v)) ⟶ V₀ v)
    (ε : V.I₀ → ULift.{u} (Fin 2))
    (π : ∀ v, Spec (.of (Polynomial (B v))) ⟶ V.X v)
    (jK : ∀ v, Spec (.of (Polynomial (B v))) ⟶ YK)
    (hV : ∀ v, IsPullback (π v) (jK v) (V.f v) q)
    (hword : ∀ v, jK v ≫ r = projectiveLinePolynomialChart (B v) (ε v) ≫
      projectiveAppendChart G i (B v) (p v) (c v))


variable (T : Subalgebra ℤ K) (hST : S ≤ T)
    (A₀ : V.I₀ → CommAlgCat.{u} S)
    (eV : ∀ v, V.X v ≅ Spec (.of (Polynomial (A₀ v))))
    (hVbase : ∀ v, ((eV v).inv ≫ V.f v) ≫ cN.pt.hom =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A₀ v)))))
    (e₀ : ∀ v, K ⊗[S] A₀ v ≃ₐ[K] B v)
    (hπ : ∀ v, π v = Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom ((e₀ v).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom))) ≫ (eV v).inv)
    (hjKb : ∀ v, jK v ≫ baseK =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial (B v)))))

include hV hword hπ hVbase hjKb in
/-- The retained matching model constructs its whole polynomial coframes
on the same coefficient stage, preserving every preceding chart leg. -/
theorem exists_matching_polynomial_coframes
    (hdata : commonMatchingCoframeData G word i S N cN hcN delta hco hn baseK q hK r EL
      V V₀ g a₀ c hend B p ε π jK T hST) :
    let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
    let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
    modelPolynomialData (T := T) N cN baseK q (matchingSingletonCover N cN hcN) V A₀ B eV e₀ jK
      r (fun v => projectiveLinePolynomialChart (B v) (ε v) ≫
        projectiveAppendChart G i (B v) (p v) (c v)) hword
      (FrobeniusSplitting.RetainedCharacter.matchingModule N cN delta 1)
      (CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) (word ++ [i])) EL
      (fun v => appendPolynomialFrame G word i (V₀ v) (g v) (a₀ v) (c v) (hend v)
        (B v) (p v) 1 (ε v)) := by
  dsimp only
  let : Algebra S T := (Subalgebra.inclusion hST).toAlgebra
  let : IsScalarTower S T K := Subalgebra.inclusion.isScalarTower_right hST K
  let W := matchingSingletonCover N cN hcN
  let C := appendCommonCover W V
  let : Finite W.I₀ := inferInstanceAs (Finite J)
  let : ∀ w, IsAffine (W.X w) := fun w =>
    inferInstanceAs (IsAffine (Spec (.of (N.obj (singletonIndex w)))))
  let : ∀ l, IsAffine (C.X l) := fun l => by
    let : IsAffine (W.X l.1) := inferInstance
    let : IsAffine (V.X l.2) := (inferInstance : ∀ v, IsAffine (V.X v)) l.2
    exact affine_fibre_product (W.f l.1) (V.f l.2)
  let : IsAffineHom q := MorphismProperty.of_isPullback hK.flip inferInstance
  let P := fun l : C.I₀ => pullback (C.f l) q
  let : ∀ l, IsAffine (P l) := fun l => inferInstance
  let : ∀ l, Algebra S Γ(C.X l, ⊤) := fun l =>
    ((C.f l ≫ cN.pt.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : ∀ l, Algebra K Γ(P l, ⊤) := fun l =>
    ((pullback.snd (C.f l) q ≫ baseK).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let j := fun l : C.I₀ => (C.X l).isoSpec.inv ≫ C.f l
  let aQ := fun l : C.I₀ => (P l).isoSpec.inv ≫ pullback.snd (C.f l) q
  obtain ⟨small, _kN, kF, e, hscalar, hsmall, hraw, _hKN, _hsN, hnative, heAll,
    _hFlat, _hFP, hstage⟩ := hdata
  let E := matchingRefinementFrame S N cN hcN delta hco hn
    (fun l : C.I₀ => Γ(C.X l, ⊤)) j (fun l => l.1) small hsmall
  let L := FrobeniusSplitting.RetainedCharacter.matchingModule N cN delta 1
  let LK := CharacterLine.wordCharacterModule G (G.positiveRootCharacter ^ 1) (word ++ [i])
  let c₀ := fun v => projectiveLinePolynomialChart (B v) (ε v) ≫
    projectiveAppendChart G i (B v) (p v) (c v)
  let Epoly := fun v => appendPolynomialFrame G word i (V₀ v) (g v) (a₀ v) (c v)
    (hend v) (B v) (p v) 1 (ε v)
  let : ∀ {s t : {s : Finset J // s.Nonempty}ᵒᵖ} (f : s ⟶ t),
      IsOpenImmersion (((N.op ⋙ algSpec (.of S)).map f).left) := fun f =>
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (N.map f.unop).hom.toRingHom)))
  let : (((N.op ⋙ algSpec (.of S)) ⋙ Over.forget (Spec (.of S))) ⋙
      Scheme.forget).IsLocallyDirected := by
    simpa only [Functor.assoc] using
      (inferInstance : ((N.op ⋙ algSpec (.of S) ⋙ Over.forget (Spec (.of S))) ⋙
        Scheme.forget).IsLocallyDirected)
  refine extend_model_frames (T := T) N cN hcN baseK q hK W V A₀ B eV e₀ jK r c₀ hword L LK EL Epoly
      ?_
  intro YT baseT qT n hqT hnT hbase hsmooth hseparated
  let : Smooth baseT := hsmooth
  let : YT.IsSeparated := hseparated
  have hjK (v : V.I₀) : jK v ≫ q = Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom ((e₀ v).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)))
          ≫
        (eV v).inv ≫ V.f v :=
    polynomial_projection (π v) (jK v) (V.f v) q _ (hπ v) (hV v).w
  exact exists_scalar_common_coframes
    (show Function.Injective (algebraMap T K) from Subtype.val_injective)
    cN.pt.hom baseT baseK qT n q hqT hnT hK hbase W V
    (fun v => (A₀ v : Type u)) (fun v => (B v : Type u)) eV hVbase e₀ jK hjK hjKb
    r c₀ hword L LK EL Epoly e
    (fun l x => tensor_one (e l) (pullback.fst (C.f l) q).appTop.hom (heAll l) x)
    kF hnative hraw E hscalar hstage.2

end Matching

end SchubertGeometry.RetainedCharacter
