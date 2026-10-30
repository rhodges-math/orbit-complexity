import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendWordCoefficients
import OrbitComplexity.SchubertGeometry.Frobenius.Assembly.AppendMatchingCover
import OrbitComplexity.SchubertGeometry.Frobenius.CharacterLine.UnitTrivialization
import OrbitComplexity.FrobeniusSplitting.Normality.Coordinates.FixedCoordinateProjection
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.Lint

/-! # Matching charts on scalar append models

The retained matching line is used on its coefficient model. Its singleton
charts and the scalar polynomial atlas admit a common affine refinement,
with the structural and section comparisons retained together.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GroupActions
open ReductiveGroups FrobeniusSplitting FrobeniusSplitting.RetainedCharacter
open scoped TensorProduct

namespace SchubertGeometry

universe u

open private singletonIndex from OrbitComplexity.FrobeniusSplitting.Modules.MatchingModule
open private singleton_chart_cover from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.MatchingPullback
open private coconeCover from
  OrbitComplexity.FrobeniusSplitting.Normality.Covers.IntersectionModelCover
open private coordinateScalarBase coordinateScalarMap from
  OrbitComplexity.SchubertGeometry.Frobenius.Assembly.WordModelSection

private theorem matching_leg_open {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [hopen : ∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (c : Cocone (N.op ⋙ algSpec (.of R))) (hc : IsColimit c)
    (s : {s : Finset J // s.Nonempty}) :
    IsOpenImmersion (c.ι.app (op s)).left := by
  let D := N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))
  let C := (Over.forget (Spec (.of R))).mapCocone c
  let : ∀ {s t} (f : s ⟶ t), IsOpenImmersion (D.map f) := fun f => hopen f.unop
  let hC : IsColimit C := isColimitOfPreserves (Over.forget (Spec (.of R))) hc
  exact (coconeCover D C hC).map_prop (op s)

private def matchingSingletonCover {R J : Type u} [CommRing R]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (c : Cocone (N.op ⋙ algSpec (.of R))) (hc : IsColimit c) :
    c.pt.left.OpenCover.{u} :=
  Scheme.Cover.mkOfCovers J (fun j => Spec (.of (N.obj (singletonIndex j))))
    (fun j => (c.ι.app (op (singletonIndex j))).left)
    (singleton_chart_cover N c hc) (fun j => matching_leg_open N c hc (singletonIndex j))

private theorem over_scalar_projection {S R : Type u} [CommRing S] [CommRing R]
    [Algebra S R] {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S))
    (C : Over (Spec (.of R)))
    (E : C ≅ Over.mk (coordinateScalarBase (R := R) base)) :
    IsPullback (E.hom.left ≫ coordinateScalarMap (R := R) base) C.hom base
      (Spec.map (CommRingCat.ofHom (algebraMap S R))) := by
  have hleft : IsPullback E.hom.left C.hom
      (coordinateScalarBase (R := R) base) (𝟙 (Spec (.of R))) :=
    IsPullback.of_horiz_isIso ⟨E.hom.w.trans (Category.comp_id _).symm⟩
  simpa only [Category.id_comp] using hleft.paste_horiz
    (IsPullback.of_hasPullback base
      (Spec.map (CommRingCat.ofHom (algebraMap S R))))

private theorem refined_old_projection {C U P Y X : Scheme.{u}}
    (a : C ⟶ U) (e : U ⟶ P) (v : U ⟶ Y) (k : P ⟶ X)
    (q : Y ⟶ X) (j : C ⟶ Y)
    (ha : a ≫ v = j) (hv : v ≫ q = e ≫ k) :
    (a ≫ e) ≫ k = j ≫ q := by
  calc
    (a ≫ e) ≫ k = a ≫ (e ≫ k) := Category.assoc _ _ _
    _ = a ≫ (v ≫ q) := congrArg (a ≫ ·) hv.symm
    _ = (a ≫ v) ≫ q := (Category.assoc _ _ _).symm
    _ = j ≫ q := congrArg (· ≫ q) ha

/-- The singleton charts of the prescribed matching diagram and the
polynomial atlas extend to a common finite affine cover of its scalar
model, retaining the old structural map and the polynomial projection. -/
theorem exists_matching_model_cover {S R J : Type u}
    [CommRing S] [CommRing R] [Algebra S R] [Finite J]
    {Y : Scheme.{u}} (base : Y ⟶ Spec (.of S)) [IsProper base] [Smooth base]
    (N : {s : Finset J // s.Nonempty} ⥤ CommAlgCat.{u} R)
    [∀ {s t} (f : s ⟶ t), IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (N.map f).hom.toRingHom))]
    [((N.op ⋙ algSpec (.of R) ⋙ Over.forget (Spec (.of R))) ⋙
      Scheme.forget).IsLocallyDirected]
    (c : Cocone (N.op ⋙ algSpec (.of R))) (hc : IsColimit c)
    (E : c.pt ≅ Over.mk (coordinateScalarBase (R := R) base))
    (U : Y.OpenCover.{u}) [Finite U.I₀]
    (A : U.I₀ → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra S (A j)]
    (eU : ∀ j, U.X j ≅ Spec (.of (Polynomial (A j))))
    (hU : ∀ j, ((eU j).inv ≫ U.f j) ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial (A j))))) :
    let W := matchingSingletonCover N c hc
    let q := E.hom.left ≫ coordinateScalarMap (R := R) base
    Finite W.I₀ ∧ (∀ j, IsAffine (W.X j)) ∧
      IsPullback q c.pt.hom base (Spec.map (CommRingCat.ofHom (algebraMap S R))) ∧
      IsProper c.pt.hom ∧ Smooth c.pt.hom ∧
      ∃ (V : c.pt.left.OpenCover.{u}) (_hfinite : Finite V.I₀)
        (_haffine : ∀ j, IsAffine (V.X j)) (index : V.I₀ ≃ U.I₀)
        (eV : ∀ j, V.X j ≅ Spec (.of (Polynomial (R ⊗[S] A (index j))))),
        (∀ j, V.f j ≫ c.pt.hom = (eV j).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial (R ⊗[S] A (index j)))))) ∧
        (∀ j, V.f j ≫ q = (eV j).hom ≫
          Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
            (Algebra.TensorProduct.includeRight : A (index j) →ₐ[S]
              R ⊗[S] A (index j)).toRingHom)) ≫
            (eU (index j)).inv ≫ U.f (index j)) ∧
        let C := appendCommonCover W V
        Finite C.I₀ ∧ ∃ hCaff : ∀ l, IsAffine (C.X l),
        ∀ l : C.I₀,
          let : IsAffine (C.X l) := hCaff l
          ∃ (a : Spec Γ(C.X l, ⊤) ⟶ W.X l.1)
            (k : Spec Γ(C.X l, ⊤) ⟶ Spec (.of (Polynomial (R ⊗[S] A (index l.2))))),
            IsOpenImmersion a ∧ IsOpenImmersion k ∧
            a ≫ W.f l.1 = (C.X l).isoSpec.inv ≫ C.f l ∧
            k ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
                (Algebra.TensorProduct.includeRight : A (index l.2) →ₐ[S]
                  R ⊗[S] A (index l.2)).toRingHom)) ≫
                (eU (index l.2)).inv ≫ U.f (index l.2) =
              ((C.X l).isoSpec.inv ≫ C.f l) ≫ q := by
  let W := matchingSingletonCover N c hc
  let q := E.hom.left ≫ coordinateScalarMap (R := R) base
  have hq : IsPullback q c.pt.hom base
      (Spec.map (CommRingCat.ofHom (algebraMap S R))) := over_scalar_projection base c.pt E
  let : IsProper c.pt.hom := MorphismProperty.of_isPullback hq inferInstance
  let : Smooth c.pt.hom := MorphismProperty.of_isPullback hq inferInstance
  let : c.pt.left.IsSeparated := ⟨by
    rw [← terminal.comp_from c.pt.hom]
    infer_instance⟩
  let : Finite W.I₀ := by
    change Finite J
    infer_instance
  let : ∀ j, IsAffine (W.X j) := by
    intro j
    let j₀ : J := j
    change IsAffine (Spec (.of (N.obj (singletonIndex j₀))))
    infer_instance
  obtain ⟨V, hfinite, haffine, index, eV, _hVcart, hVbase, hVold⟩ :=
    exists_append_scalar_cover base c.pt.hom q hq U A eU hU
  let : Finite V.I₀ := hfinite
  let : ∀ j, IsAffine (V.X j) := haffine
  let C := appendCommonCover W V
  refine ⟨inferInstance, inferInstance, hq, inferInstance, inferInstance,
    V, hfinite, haffine, index, eV, hVbase, hVold, inferInstance, inferInstance, ?_⟩
  intro l
  let a := (C.X l).isoSpec.inv ≫ appendCommonLeft W V l
  let b := (C.X l).isoSpec.inv ≫ appendCommonRight W V l
  have ha : a ≫ W.f l.1 = (C.X l).isoSpec.inv ≫ C.f l :=
    (Category.assoc _ _ _).trans
      (congrArg ((C.X l).isoSpec.inv ≫ ·) (appendCommonLeft_map W V l))
  have hb : b ≫ V.f l.2 = (C.X l).isoSpec.inv ≫ C.f l :=
    (Category.assoc _ _ _).trans
      (congrArg ((C.X l).isoSpec.inv ≫ ·) (appendCommonRight_map W V l))
  let k := b ≫ (eV l.2).hom
  have hbold := refined_old_projection b (eV l.2).hom (V.f l.2)
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Algebra.TensorProduct.includeRight : A (index l.2) →ₐ[S]
        R ⊗[S] A (index l.2)).toRingHom)) ≫
      (eU (index l.2)).inv ≫ U.f (index l.2)) q
    ((C.X l).isoSpec.inv ≫ C.f l) hb (hVold l.2)
  exact ⟨a, k, inferInstance, inferInstance, ha, by
    simpa only [k, q, Category.assoc] using hbold⟩

end SchubertGeometry
