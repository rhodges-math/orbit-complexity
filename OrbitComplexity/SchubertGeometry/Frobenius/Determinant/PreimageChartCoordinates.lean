import OrbitComplexity.SchubertGeometry.Frobenius.Determinant.PreimageMatchingCover
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.AffineChartPresentation

/-! # Coordinates on matching preimage charts

A finite affine refinement of a smooth preimage carries its original matching
projection and the tensor-product coordinates of its scalar pullback.
-/

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FrobeniusSplitting
open scoped TensorProduct

namespace SchubertGeometry.RetainedCharacter

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private SchubertGeometry.common_field_coordinates from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover

private theorem affineChartPullback {X Y Z : Scheme.{u}}
    (g : X ⟶ Z) (n : Y ⟶ Z) [IsAffine X] [IsAffineHom n] :
    IsAffine (pullback g n) := by
  let : IsAffineHom (pullback.fst g n) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback g n).flip inferInstance
  exact isAffine_of_isAffineHom (pullback.fst g n)

private theorem coordinateTriangle {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] {X P Y Z : Scheme.{u}} [IsAffine X] [IsAffine P]
    (q : P ⟶ X) (g : X ⟶ Z) (a : P ⟶ Y) (n : Y ⟶ Z)
    (h : q ≫ g = a ≫ n)
    [Algebra R Γ(X, ⊤)] [Algebra K Γ(P, ⊤)]
    (e : K ⊗[R] Γ(X, ⊤) ≃ₐ[K] Γ(P, ⊤))
    (he : ∀ x, e ((1 : K) ⊗ₜ[R] x) = q.appTop.hom x) :
    Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
        (X.isoSpec.inv ≫ g) = (P.isoSpec.inv ≫ a) ≫ n := by
  have hring : e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      q.appTop.hom := RingHom.ext he
  have hq : Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ X.isoSpec.inv =
      P.isoSpec.inv ≫ q := by
    rw [hring]
    exact Scheme.isoSpec_inv_naturality q
  calc
    _ = (Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
          X.isoSpec.inv) ≫ g := (Category.assoc _ _ _).symm
    _ = (P.isoSpec.inv ≫ q) ≫ g := congrArg (fun z => z ≫ g) hq
    _ = P.isoSpec.inv ≫ (q ≫ g) := Category.assoc _ _ _
    _ = P.isoSpec.inv ≫ (a ≫ n) := congrArg (P.isoSpec.inv ≫ ·) h
    _ = (P.isoSpec.inv ≫ a) ≫ n := (Category.assoc _ _ _).symm

private theorem coordinateRefinement {X Z W : Scheme.{u}} [IsAffine X]
    (b : X ⟶ Z) (l : Z ⟶ W) (g : X ⟶ W) (h : b ≫ l = g) :
    (X.isoSpec.inv ≫ b) ≫ l = X.isoSpec.inv ≫ g := by
  rw [Category.assoc, h]

variable {S0 J : Type u} [CommRing S0]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} S0)
    [hOpen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [hDirected : ((N.op ⋙ algSpec (.of S0) ⋙ Over.forget (Spec (.of S0))) ⋙
      Scheme.forget).IsLocallyDirected]
    (cN : Cocone (N.op ⋙ algSpec (.of S0))) (hcN : IsColimit cN)
    (delta : ∀ (s : {s : Finset J // s.Nonempty}) (j : J) (_ : j ∈ s.val)
      (k : J) (_ : k ∈ s.val), (N.obj s)ˣ)
    (hco : ∀ s j hj k hk l hl,
      delta s j hj l hl = delta s k hk l hl * delta s j hj k hk)
    (hn : ∀ s t (f : s ⟶ t) j hj k hk,
      Units.map (N.map f).hom.toMonoidHom (delta s j hj k hk) =
        delta t j ((leOfHom f) hj) k ((leOfHom f) hk))

include hOpen hDirected hcN delta hco hn

/-- The finite matching refinement of a smooth preimage has flat, finitely
presented coordinate rings and their canonical scalar tensor comparisons. -/
theorem exists_preimage_chart_coordinates {R K : Type u}
    [CommRing R] [CommRing K] [Algebra R K]
    (hR : Function.Injective (algebraMap R K))
    {Y YK : Scheme.{u}} [CompactSpace Y]
    (base : Y ⟶ Spec (.of R)) [Smooth base]
    (baseK : YK ⟶ Spec (.of K)) (n : YK ⟶ Y)
    (hK : IsPullback n baseK base
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (j : Y ⟶ cN.pt.left) :
    ∃ (V : Y.OpenCover.{u}) (_hfinite : Finite V.I₀)
      (haffine : ∀ l, IsAffine (V.X l)) (index : V.I₀ → J)
      (b : ∀ l, V.X l ⟶ Spec (.of (N.obj (singletonIndex (index l)))))
      (_h : ∀ l, b l ≫ (cN.ι.app (op (singletonIndex (index l)))).left = V.f l ≫ j),
      ∀ l : V.I₀,
        let P : Scheme.{u} := pullback (V.f l) n
        letI : IsAffine (V.X l) := haffine l
        letI : IsAffineHom n :=
          MorphismProperty.of_isPullback (P := @IsAffineHom) hK.flip inferInstance
        letI : IsAffine P := affineChartPullback (V.f l) n
        let f := V.f l ≫ base
        let t := pullback.snd (V.f l) n ≫ baseK
        let q := pullback.fst (V.f l) n
        letI : Algebra R Γ(V.X l, ⊤) :=
          (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
        letI : Algebra K Γ(P, ⊤) :=
          (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
        Module.Flat R Γ(V.X l, ⊤) ∧ Algebra.FinitePresentation R Γ(V.X l, ⊤) ∧
        Function.Injective q.appTop.hom ∧
        ((V.X l).isoSpec.inv ≫ b l) ≫
          (cN.ι.app (op (singletonIndex (index l)))).left =
            (V.X l).isoSpec.inv ≫ (V.f l ≫ j) ∧
        ∃ e : K ⊗[R] Γ(V.X l, ⊤) ≃ₐ[K] Γ(P, ⊤),
          (∀ x, e ((1 : K) ⊗ₜ[R] x) = q.appTop.hom x) ∧
          Spec.map (CommRingCat.ofHom
            (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫
              ((V.X l).isoSpec.inv ≫ (V.f l ≫ j)) =
                (P.isoSpec.inv ≫ pullback.snd (V.f l) n) ≫ (n ≫ j) := by
  obtain ⟨V, hfinite, haffine, index, b, h, _, _⟩ :=
    exists_matching_preimage_cover N cN hcN delta hco hn j
  refine ⟨V, hfinite, haffine, index, b, h, ?_⟩
  intro l
  let P : Scheme.{u} := pullback (V.f l) n
  let : IsAffine (V.X l) := haffine l
  let : IsAffineHom n :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hK.flip inferInstance
  let : IsAffine P := affineChartPullback (V.f l) n
  let f := V.f l ≫ base
  let t := pullback.snd (V.f l) n ≫ baseK
  let q := pullback.fst (V.f l) n
  let : Algebra R Γ(V.X l, ⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra K Γ(P, ⊤) :=
    (t.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let : Smooth f := inferInstanceAs (Smooth (V.f l ≫ base))
  have hchart : IsPullback q t f
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    (IsPullback.of_hasPullback (V.f l) n).paste_vert hK
  obtain ⟨hflat, hinjective, e, _, he, _⟩ :=
    SchubertGeometry.common_field_coordinates hR f t q hchart
  have hpresentation : Algebra.FinitePresentation R Γ(V.X l, ⊤) :=
    finitePresentation_chartSections f
  refine ⟨hflat, hpresentation, hinjective, coordinateRefinement (b l) _ _ (h l), e, he, ?_⟩
  apply coordinateTriangle q (V.f l ≫ j) (pullback.snd (V.f l) n) (n ≫ j)
    _ e he
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ j) (pullback.condition (f := V.f l) (g := n))).trans
      (Category.assoc _ _ _))

end SchubertGeometry.RetainedCharacter
