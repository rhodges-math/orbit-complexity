import OrbitComplexity.FrobeniusSplitting.Normality.Limits.AffineFamilyStages
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ClosedAffineStages
import OrbitComplexity.FrobeniusSplitting.Normality.Models.ModelScalarExtension
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Separated coefficient stages

A Noetherian finite type model with separated generic fibre becomes separated
after increasing its finitely generated coefficient ring.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FrobeniusSplitting

universe u

private theorem affine_iso_source {A B : Scheme.{u}} (E : A ≅ B) [IsAffine B] :
    IsAffine A := isAffine_of_isAffineHom E.hom

private theorem affine_product {B A C : Scheme.{u}} [IsAffine B]
    (f : A ⟶ B) (g : C ⟶ B) (hA : IsAffine A) (hC : IsAffine C) :
    IsAffine (pullback f g : Scheme.{u}) := by
  let : IsAffine A := hA
  let : IsAffine C := hC
  infer_instance

private theorem affine_overlap {B X : Scheme.{u}} [IsAffine B]
    (s : X ⟶ B) [IsSeparated s] (U : X.OpenCover.{u})
    [∀ i, IsAffine (U.X i)] (i j : U.I₀) :
    IsAffine (pullback (U.f i) (U.f j) : Scheme.{u}) := by
  let p := pullback.mapDesc (U.f i) (U.f j) s
  let : IsClosedImmersion p := inferInstance
  exact isAffine_of_isAffineHom p

private theorem affine_scalar_charts {B T X : Scheme.{u}} [IsAffine B] [IsAffine T]
    (κ : T ⟶ B) (s : X ⟶ B) (U : X.OpenCover.{u})
    [∀ i, IsAffine (U.X i)] (i : U.I₀) :
    IsAffine ((U.pullback₁ (pullback.snd κ s)).X i) := by
  let E := pullbackLeftPullbackSndIso κ s (U.f i)
  let : IsAffine (pullback κ (U.f i ≫ s) : Scheme.{u}) := inferInstance
  exact affine_iso_source E

private theorem graph_closed {B X : Scheme.{u}}
    (s : X ⟶ B) [IsSeparated s] (U : X.OpenCover.{u}) (i j : U.I₀) :
    IsClosedImmersion (coverOverlapGraph U s i j) := by
  have he : coverOverlapGraph U s i j = pullback.mapDesc (U.f i) (U.f j) s := by
    apply pullback.hom_ext <;> simp [coverOverlapGraph, pullback.mapDesc, pullback.map]
  rw [he]
  infer_instance

private theorem scalar_graph_closed {B T X : Scheme.{u}}
    (κ : T ⟶ B) (s : X ⟶ B) (U : X.OpenCover.{u})
    [IsSeparated (pullback.fst κ s)] (i j : U.I₀) :
    IsClosedImmersion (scalarCoverGraph κ s U i j) := by
  let V : (pullback κ s).OpenCover.{u} := U.pullback₁ (pullback.snd κ s)
  let E := scalarCoverOverlapIso κ s U i j
  let P := (scalar_product_square κ s U i j).flip.isoPullback
  let : IsClosedImmersion (coverOverlapGraph V (pullback.fst κ s) i j) :=
    graph_closed (pullback.fst κ s) V i j
  have he : scalarCoverGraph κ s U i j =
      E.inv ≫ coverOverlapGraph V (pullback.fst κ s) i j ≫ P.hom := by
    have hc : coverOverlapGraph V (pullback.fst κ s) i j ≫ P.hom =
        E.hom ≫ scalarCoverGraph κ s U i j := graph_comparison κ s U i j
    have h := congrArg (fun z => E.inv ≫ z) hc
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  rw [he]
  infer_instance

private theorem separated_iso {T X Y : Scheme.{u}}
    (E : X ≅ Y) (a : X ⟶ T) (b : Y ⟶ T) (h : E.hom ≫ b = a) :
    IsSeparated a ↔ IsSeparated b := by
  rw [← h]
  exact MorphismProperty.cancel_left_of_respectsIso @IsSeparated E.hom b

private theorem separated_tower {B R T X : Scheme.{u}}
    (ρ : R ⟶ B) (σ : T ⟶ R) (κ : T ⟶ B) (h : σ ≫ ρ = κ) (s : X ⟶ B) :
    IsSeparated (pullback.fst σ (pullback.fst ρ s)) ↔
      IsSeparated (pullback.fst κ s) := by
  let E := pullbackRightPullbackFstIso ρ s σ ≪≫ pullback.congrHom h rfl
  have he : E.hom ≫ pullback.fst κ s = pullback.fst σ (pullback.fst ρ s) := by
    simp [E]
  exact separated_iso E _ _ he

private theorem inclusion_spec_comp {K : Type u} [Field K]
    (S R : Subalgebra ℤ K) (hSR : S ≤ R) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hSR).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) := by
  rw [← Spec.map_comp]
  congr 1

private theorem inclusion_spec_tower {K : Type u} [Field K]
    (S R T : Subalgebra ℤ K) (hSR : S ≤ R) (hRT : R ≤ T) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRT).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hSR).toRingHom) =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hSR.trans hRT)).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1

private theorem cover_overlap_compact {X : Scheme.{u}} [IsNoetherian X]
    (U : X.OpenCover.{u}) (i j : U.I₀) :
    CompactSpace (pullback (U.f i) (U.f j) : Scheme.{u}) := by
  let inc := pullback.fst (U.f i) (U.f j) ≫ U.f i
  let : IsOpenImmersion inc := inferInstance
  let : NoetherianSpace (pullback (U.f i) (U.f j) : Scheme.{u}) :=
    inc.isOpenEmbedding.isInducing.noetherianSpace
  infer_instance

private theorem cover_overlap_qs {X : Scheme.{u}} [IsNoetherian X]
    (U : X.OpenCover.{u}) (i j : U.I₀) :
    QuasiSeparatedSpace (pullback (U.f i) (U.f j) : Scheme.{u}) := by
  let inc := pullback.fst (U.f i) (U.f j) ≫ U.f i
  let : IsOpenImmersion inc := inferInstance
  let : IsLocallyNoetherian (pullback (U.f i) (U.f j) : Scheme.{u}) :=
    isLocallyNoetherian_of_isOpenImmersion inc
  infer_instance

private theorem overlap_finiteType {B X : Scheme.{u}}
    (s : X ⟶ B) [LocallyOfFiniteType s] (U : X.OpenCover.{u}) (i j : U.I₀) :
    LocallyOfFiniteType (pullback.fst (U.f i) (U.f j) ≫ U.f i ≫ s) := by
  infer_instance

private theorem graph_structure {B X : Scheme.{u}} (s : X ⟶ B)
    (U : X.OpenCover.{u}) (i j : U.I₀) :
    coverOverlapGraph U s i j ≫
        (pullback.fst (U.f i ≫ s) (U.f j ≫ s) ≫ (U.f i ≫ s)) =
      pullback.fst (U.f i) (U.f j) ≫ U.f i ≫ s := by
  rw [← Category.assoc, coverOverlapGraph_fst]

/-- A Noetherian finite type model with separated generic fibre has a separated
coefficient stage above any prescribed starting stage. -/
theorem exists_separated_scalar_stage
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    (X : Over (Spec (.of S))) [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
    [IsSeparated (genericScalarModel S X.hom).hom] (start : CoefficientStage S) :
    ∃ (j : CoefficientStage S), start ≤ j ∧ IsSeparated (stageScalarModel S X.hom j).hom := by
  classical
  let U : X.left.OpenCover.{u} := X.left.affineCover.finiteSubcover
  let : Finite U.I₀ := inferInstance
  let (i : U.I₀) : IsAffine (U.X i) := by
    dsimp [U, Scheme.OpenCover.finiteSubcover]
    infer_instance
  let J := U.I₀ × U.I₀
  let A (ij : J) : Over (Spec (.of S)) :=
    Over.mk (pullback.fst (U.f ij.1) (U.f ij.2) ≫ U.f ij.1 ≫ X.hom)
  let (ij : J) : CompactSpace (A ij).left := cover_overlap_compact U ij.1 ij.2
  let (ij : J) : QuasiSeparatedSpace (A ij).left := cover_overlap_qs U ij.1 ij.2
  let κK := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let VK : (pullback κK X.hom).OpenCover.{u} := U.pullback₁ (pullback.snd κK X.hom)
  let (i : VK.I₀) : IsAffine (VK.X i) := affine_scalar_charts κK X.hom U i
  let : IsSeparated (pullback.fst κK X.hom) := inferInstanceAs
    (IsSeparated (genericScalarModel S X.hom).hom)
  let (ij : J) : IsAffine (genericScalarModel S (A ij).hom).left := by
    let E := scalarCoverOverlapIso κK X.hom U ij.1 ij.2
    let : IsAffine (pullback (VK.f ij.1) (VK.f ij.2) : Scheme.{u}) :=
      affine_overlap (pullback.fst κK X.hom) VK ij.1 ij.2
    exact affine_iso_source E.symm
  obtain ⟨r, hstart, haff⟩ := exists_affine_family_stage S hS A start
  let R := r.val
  let ρ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom)
  let sR : pullback ρ X.hom ⟶ Spec (.of R) := pullback.fst ρ X.hom
  let V : (pullback ρ X.hom).OpenCover.{u} := U.pullback₁ (pullback.snd ρ X.hom)
  let (i : V.I₀) : IsAffine (V.X i) := affine_scalar_charts ρ X.hom U i
  have hoverlap (ij : J) : IsAffine (pullback (V.f ij.1) (V.f ij.2) : Scheme.{u}) := by
    let E := scalarCoverOverlapIso ρ X.hom U ij.1 ij.2
    exact @affine_iso_source _ _ E (haff ij)
  let B (ij : J) : Over (Spec (.of R)) :=
    Over.mk (pullback.fst (V.f ij.1) (V.f ij.2) ≫ V.f ij.1 ≫ sR)
  let C (ij : J) : Over (Spec (.of R)) :=
    Over.mk (pullback.fst (V.f ij.1 ≫ sR) (V.f ij.2 ≫ sR) ≫ (V.f ij.1 ≫ sR))
  let f (ij : J) : B ij ⟶ C ij :=
    Over.homMk (coverOverlapGraph V sR ij.1 ij.2) (graph_structure sR V ij.1 ij.2)
  let (ij : J) : IsAffine (B ij).left := hoverlap ij
  let (ij : J) : IsAffine (C ij).left :=
    affine_product (V.f ij.1 ≫ sR) (V.f ij.2 ≫ sR)
      (affine_scalar_charts ρ X.hom U ij.1) (affine_scalar_charts ρ X.hom U ij.2)
  let : LocallyOfFiniteType sR := inferInstance
  let (ij : J) : LocallyOfFiniteType (B ij).hom := overlap_finiteType sR V ij.1 ij.2
  let σK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let : IsSeparated (pullback.fst σK sR) :=
    (separated_tower ρ σK κK (inclusion_spec_comp S R r.property.2) X.hom).mpr inferInstance
  have hclosed (ij : J) : IsClosedImmersion (affineScalarMap σK (f ij)) :=
    scalar_graph_closed σK sR V ij.1 ij.2
  let startR : CoefficientStage R := ⟨R, r.property.1, le_rfl⟩
  obtain ⟨t, _, hgraphs⟩ := exists_closed_affine_stage R r.property.1 B C f hclosed startR
  let τ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion t.property.2).toRingHom)
  let : IsSeparated (pullback.fst τ sR) :=
    separated_scalar_of_graphs τ sR V (fun i j => hgraphs (i, j))
  let j : CoefficientStage S := ⟨t.val, t.property.1, r.property.2.trans t.property.2⟩
  refine ⟨j, hstart.trans t.property.2, ?_⟩
  exact (separated_tower ρ τ
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion j.property.2).toRingHom))
    (inclusion_spec_tower S R t.val r.property.2 t.property.2) X.hom).mp inferInstance

end FrobeniusSplitting
