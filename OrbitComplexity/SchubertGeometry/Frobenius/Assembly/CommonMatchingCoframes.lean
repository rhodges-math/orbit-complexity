import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingAppendCoframes
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineChartPresentation
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Retained coframes on the common matching charts

The common affine coordinates give the coefficient algebras, scalar maps
and polynomial maps over the field used to retain the matching coframes. The
original matching diagram and line module are kept throughout.
-/

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ReductiveGroups GroupActions FrobeniusSplitting
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private matchingSingletonCover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingModel
open private affine_fibre_product from
  OrbitComplexity.FrobeniusSplitting.Normality.Assembly.FrameCoverRefinement

namespace SchubertGeometry.RetainedCharacter

private theorem chart_scalar_square {S K : Type u}
    [CommRing S] [CommRing K] [Algebra S K]
    {X P Y : Scheme.{u}} [IsAffine X] [IsAffine P]
    [Algebra S Γ(X, ⊤)] [Algebra K Γ(P, ⊤)]
    (e : K ⊗[S] Γ(X, ⊤) ≃ₐ[K] Γ(P, ⊤))
    (q : P ⟶ X) (i : X ⟶ Y) (n : P ⟶ Y) (h : q ≫ i = n)
    (he : ∀ x, e ((1 : K) ⊗ₜ[S] x) = q.appTop.hom x) :
    Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ X.isoSpec.inv ≫ i =
      P.isoSpec.inv ≫ n := by
  have hm : e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom = q.appTop.hom := by
    ext x
    exact he x
  rw [hm]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ i) (Scheme.isoSpec_inv_naturality q)).trans
      ((Category.assoc _ _ _).trans (congrArg (fun t => P.isoSpec.inv ≫ t) h)))

section Coordinates

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

/-- The original common coordinates and matching coframes at one coefficient stage. -/
def commonMatchingCoframeData (T : Subalgebra ℤ K) (hST : S ≤ T) : Prop :=
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
  let M : C.I₀ → Type u := fun l => Γ(C.X l, ⊤)
  let A : C.I₀ → Type u := fun l => Γ(P l, ⊤)
  let : ∀ l, Algebra S (M l) := fun l =>
    ((C.f l ≫ cN.pt.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : ∀ l, Algebra K (A l) := fun l =>
    ((pullback.snd (C.f l) q ≫ baseK).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let j := fun l : C.I₀ => (C.X l).isoSpec.inv ≫ C.f l
  let jF := fun l : C.I₀ => (P l).isoSpec.inv ≫ pullback.snd (C.f l) q
  ∃ (small : ∀ l : C.I₀, Spec (.of (M l)) ⟶ W.X l.1)
    (kN : ∀ l : C.I₀, Spec (.of (M l)) ⟶ V.X l.2)
    (kF : ∀ l : C.I₀, Spec (.of (A l)) ⟶ Spec (.of (Polynomial (B l.2))))
    (e : ∀ l : C.I₀, K ⊗[S] M l ≃ₐ[K] A l)
    (hscalar : ∀ l, Spec.map (CommRingCat.ofHom
      ((e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ j l = jF l ≫ q)
    (hsmall : ∀ l, j l = small l ≫ (cN.ι.app (op (singletonIndex l.1))).left)
    (hk : ∀ l, jF l ≫ r = kF l ≫ projectiveLinePolynomialChart (B l.2) (ε l.2) ≫
      projectiveAppendChart G i (B l.2) (p l.2) (c l.2)),
    (∀ l, kN l ≫ V.f l.2 = j l) ∧
    (∀ l, Spec.map (pullback.fst (C.f l) q).appTop ≫ kN l = kF l ≫ π l.2) ∧
    (∀ l, kF l ≫ jK l.2 = jF l) ∧
    (∀ l k x, e l (k ⊗ₜ[S] x) =
      algebraMap K (A l) k * (pullback.fst (C.f l) q).appTop.hom x) ∧
    (∀ l, Module.Flat S (M l)) ∧ (∀ l, Algebra.FinitePresentation S (M l)) ∧
    matchingAppendCoframeStage G word i S N cN hcN delta hco hn M A e q r EL
      j jF hscalar (fun l => l.1) small hsmall
      (fun l => V₀ l.2) (fun l => g l.2) (fun l => a₀ l.2) (fun l => c l.2)
      (fun l => hend l.2) (fun l => B l.2) (fun l => p l.2)
      (fun l => ε l.2) kF hk T hST

include hword in
omit [Finite V.I₀] in
/-- The common affine-coordinate certificate constructs the fine matching
coframes and retains their units over one coefficient extension. -/
theorem exists_common_matching_coframes (hS : S.FG)
    (hcoords :
      let W := matchingSingletonCover N cN hcN
      let : Finite W.I₀ := inferInstanceAs (Finite J)
      let : ∀ w, IsAffine (W.X w) := fun w =>
        inferInstanceAs (IsAffine (Spec (.of (N.obj (singletonIndex w)))))
      type_of% (exists_append_matching_coordinates
      (show Function.Injective (algebraMap S K) from Subtype.val_injective)
      cN.pt.hom baseK q hK (matchingSingletonCover N cN hcN) V
      (fun v => Spec (.of (Polynomial (B v)))) π jK hV)) :
    ∃ (T : Subalgebra ℤ K) (hST : S ≤ T), T.FG ∧
      commonMatchingCoframeData G word i S N cN hcN delta hco hn baseK q hK r EL
        V V₀ g a₀ c hend B p ε π jK T hST := by
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
  let M : C.I₀ → Type u := fun l => Γ(C.X l, ⊤)
  let A : C.I₀ → Type u := fun l => Γ(P l, ⊤)
  let : ∀ l, Algebra S (M l) := fun l =>
    ((C.f l ≫ cN.pt.hom).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom).toAlgebra
  let : ∀ l, Algebra K (A l) := fun l =>
    ((pullback.snd (C.f l) q ≫ baseK).appTop.hom.comp
      (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let j := fun l : C.I₀ => (C.X l).isoSpec.inv ≫ C.f l
  let jF := fun l : C.I₀ => (P l).isoSpec.inv ≫ pullback.snd (C.f l) q
  let : Finite C.I₀ := hcoords.1
  choose small kN kF hsmallOpen hKNOpen hsmallRaw hKNRaw hscalarKN hNative hFlat hInj
    e heLeft heRight heAll using hcoords.2
  let : ∀ l, Module.Flat S (M l) := hFlat
  let : ∀ l, Algebra.FinitePresentation S (M l) := fun l => by
    let : Smooth (C.f l ≫ cN.pt.hom) := inferInstance
    exact FrobeniusSplitting.finitePresentation_chartSections (C.f l ≫ cN.pt.hom)
  have hsmall : ∀ l, j l = small l ≫ (cN.ι.app (op (singletonIndex l.1))).left :=
    fun l => (hsmallRaw l).symm
  have hscalar : ∀ l, Spec.map (CommRingCat.ofHom
      ((e l).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ j l = jF l ≫ q := by
    intro l
    exact chart_scalar_square (e l) (pullback.fst (C.f l) q) (C.f l)
      (pullback.snd (C.f l) q ≫ q) (pullback.condition (f := C.f l) (g := q))
      (heRight l)
  have hk : ∀ l, jF l ≫ r = kF l ≫ projectiveLinePolynomialChart (B l.2) (ε l.2) ≫
      projectiveAppendChart G i (B l.2) (p l.2) (c l.2) := by
    intro l
    calc
      _ = (kF l ≫ jK l.2) ≫ r := congrArg (fun t => t ≫ r) (hNative l).symm
      _ = _ := (Category.assoc _ _ _).trans
        (congrArg (fun t => kF l ≫ t) (hword l.2))
  obtain ⟨T, hST, hstage⟩ := exists_matching_append_coframes G word i S N cN hcN
    delta hco hn M A e q r EL j jF hscalar (fun l => l.1) small hsmall
    (fun l => V₀ l.2) (fun l => g l.2) (fun l => a₀ l.2) (fun l => c l.2)
    (fun l => hend l.2) (fun l => B l.2) (fun l => p l.2) (fun l => ε l.2) kF hk hS
  refine ⟨T, hST, hstage.1, small, kN, kF, e, hscalar, hsmall, hk,
    hKNRaw, hscalarKN, hNative, heAll, hFlat, ?_, hstage⟩
  exact fun l => inferInstance

end Coordinates

end SchubertGeometry.RetainedCharacter
