import OrbitComplexity.SchubertGeometry.Connectedness.CellMapRetention
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.AppendFibreModels
import OrbitComplexity.SchubertGeometry.Connectedness.RestrictedCurveStage
import OrbitComplexity.SchubertGeometry.Connectedness.CellGeometric
import OrbitComplexity.SchubertGeometry.Normality.Cells.CellProducts
import OrbitComplexity.GroupActions.Varieties.ProjectiveChartsSmooth
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedIsomorphisms
import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps

set_option autoImplicit false

/-! # Elementary intersections for the appended endpoint

The two simple-curve alternatives determine the field fibres of the same
closed intersection. Whole-curve comparisons and restricted-chart equations
are extended through the specified coefficient models.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting GroupActions Opposite SchubertGeometry.CellContraction
open CartesianMonoidalCategory MonoidalCategory

namespace SchubertGeometry

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Over.cartesianMonoidalCategory

private theorem pullback_model_properties
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Z F C : Over (Spec (.of R))}
    [CompactSpace Z.left] [CompactSpace C.left]
    [LocallyOfFinitePresentation Z.hom] [LocallyOfFinitePresentation F.hom]
    [LocallyOfFinitePresentation C.hom] (f : Z ⟶ F) (c : C ⟶ F) :
    LocallyOfFinitePresentation (pullback.snd f.left c.left ≫ C.hom) ∧
      CompactSpace (pullback f.left c.left : Scheme.{u}) ∧
      QuasiSeparatedSpace (pullback f.left c.left : Scheme.{u}) := by
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
  let : AlgebraicGeometry.IsNoetherian Z.left := AlgebraicGeometry.IsNoetherian.mk
  let : LocallyOfFiniteType (f.left ≫ F.hom) := f.w.symm ▸ inferInstanceAs
    (LocallyOfFiniteType Z.hom)
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left F.hom
  let : LocallyOfFinitePresentation f.left := inferInstance
  let : QuasiCompact f.left := inferInstance
  let : LocallyOfFinitePresentation (pullback.snd f.left c.left) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f.left c.left) inferInstance
  let : QuasiCompact (pullback.snd f.left c.left) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f.left c.left) inferInstance
  let : LocallyOfFinitePresentation (pullback.snd f.left c.left ≫ C.hom) := inferInstance
  let : CompactSpace (pullback f.left c.left : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f.left c.left)
  let : IsLocallyNoetherian (pullback f.left c.left : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f.left c.left ≫ C.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem product_model_properties
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C W : Over (Spec (.of R))) [CompactSpace C.left]
    [LocallyOfFinitePresentation C.hom] [LocallyOfFinitePresentation W.hom]
    [QuasiCompact W.hom] :
    LocallyOfFinitePresentation (C ⊗ W).hom ∧ CompactSpace (C ⊗ W).left ∧
      QuasiSeparatedSpace (C ⊗ W).left := by
  let : LocallyOfFinitePresentation (pullback.fst C.hom W.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback C.hom W.hom).flip inferInstance
  let : QuasiCompact (pullback.fst C.hom W.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback C.hom W.hom).flip inferInstance
  let : LocallyOfFinitePresentation (C ⊗ W).hom := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.fst C.hom W.hom ≫ C.hom))
  let : CompactSpace (C ⊗ W).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst C.hom W.hom)
  let : IsLocallyNoetherian (C ⊗ W).left :=
    LocallyOfFiniteType.isLocallyNoetherian (C ⊗ W).hom
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem scalar_endpoint_eq {B T : Scheme.{u}} (κ : T ⟶ B)
    {X P D : Over B} (E : Over.mk (pullback.fst κ X.hom) ≅
      Over.mk (pullback.fst κ P.hom)) (u : X ⟶ D) (v : P ⟶ D)
    (h : E.hom.left ≫ pullback.snd κ P.hom ≫ v.left =
      pullback.snd κ X.hom ≫ u.left) :
    E.hom ≫ chosenScalarArrow κ v = chosenScalarArrow κ u := by
  apply (Over.forget T).map_injective
  change E.hom.left ≫ (chosenScalarArrow κ v).left = (chosenScalarArrow κ u).left
  apply pullback.hom_ext
  · exact (E.hom ≫ chosenScalarArrow κ v).w.trans (chosenScalarArrow κ u).w.symm
  · calc
      (E.hom.left ≫ (chosenScalarArrow κ v).left) ≫ pullback.snd κ D.hom =
          E.hom.left ≫ (pullback.snd κ P.hom ≫ v.left) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => E.hom.left ≫ k) (chosenScalarArrow_snd κ v))
      _ = pullback.snd κ X.hom ≫ u.left := h
      _ = (chosenScalarArrow κ u).left ≫ pullback.snd κ D.hom :=
        (chosenScalarArrow_snd κ u).symm

private theorem inverse_triangle {T : Type*} [Category T]
    {X P D : T} (E : X ≅ P) (u : X ⟶ D) (v : P ⟶ D)
    (h : E.hom ≫ v = u) : E.inv ≫ u = v :=
  (congrArg (fun f => E.inv ≫ f) h.symm).trans (E.inv_hom_id_assoc v)

private theorem mapped_triangle {T U : Type*} [Category T] [Category U]
    {A B C : T} {A' B' C' : U} (f : A ⟶ B) (u : A ⟶ C) (v : B ⟶ C)
    (F : (A ⟶ B) → (A' ⟶ B')) (G : (B ⟶ C) → (B' ⟶ C'))
    (H : (A ⟶ C) → (A' ⟶ C')) (f' : A' ⟶ B') (u' : A' ⟶ C') (v' : B' ⟶ C')
    (hf : F f = f') (hv : G v = v') (hu : H u = u')
    (hcomp : F f ≫ G v = H (f ≫ v)) (h : f ≫ v = u) : f' ≫ v' = u' :=
  (congrArg (fun k => k ≫ v') hf.symm).trans
    ((congrArg (fun k => F f ≫ k) hv.symm).trans
      (hcomp.trans ((congrArg H h).trans hu)))

private def cell_stage_result
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) {J : Type v}
    (X P D : J → Over (Spec (.of S))) (u : ∀ r, X r ⟶ D r) (v : ∀ r, P r ⟶ D r)
    (start : CoefficientStage S) : Prop :=
  ∃ (E : ∀ r, genericScalarModel S (X r).hom ≅ genericScalarModel S (P r).hom)
    (k : CoefficientStage S) (_ : start ≤ k)
    (E₀ : ∀ r, stageScalarModel S (X r).hom k ≅ stageScalarModel S (P r).hom k),
    (∀ r, (modelScalarCone S (X r).hom).π.app (op k) ≫ (E₀ r).hom.left =
      (E r).hom.left ≫ (modelScalarCone S (P r).hom).π.app (op k)) ∧
    (∀ r, (modelScalarCone S (P r).hom).π.app (op k) ≫ (E₀ r).inv.left =
      (E r).inv.left ≫ (modelScalarCone S (X r).hom).π.app (op k)) ∧
    (∀ r, (E₀ r).hom ≫ chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) (v r) =
        chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) (u r)) ∧
    ∀ r, (E₀ r).inv ≫ chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) (u r) =
        chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) (v r)

private theorem retain_cell_family
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type v} [Fintype J] (X P D : J → Over (Spec (.of S)))
    [∀ r, CompactSpace (X r).left] [∀ r, QuasiSeparatedSpace (X r).left]
    [∀ r, CompactSpace (P r).left] [∀ r, QuasiSeparatedSpace (P r).left]
    [∀ r, LocallyOfFinitePresentation (X r).hom]
    [∀ r, LocallyOfFinitePresentation (P r).hom]
    [∀ r, LocallyOfFiniteType (D r).hom]
    (u : ∀ r, X r ⟶ D r) (v : ∀ r, P r ⟶ D r)
    (hE : ∀ r, ∃ E : genericScalarModel S (X r).hom ≅ genericScalarModel S (P r).hom,
      E.hom ≫ chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap S K))) (v r) =
        chosenScalarArrow (Spec.map (CommRingCat.ofHom (algebraMap S K))) (u r))
    (start : CoefficientStage S) : cell_stage_result S X P D u v start := by
  classical
  choose E hE using hE
  have hs := fun r => exists_chosen_endpoint_iso S hS (X r) (P r) (D r)
    (u r) (v r) (E r) (hE r) start
  choose i hi E₀ hhom hinv hend using hs
  obtain ⟨k, hstart, hik⟩ := curveFamily_upper_stage i start
  let E₁ (r : J) := curveFamilyExtendIso S (X r).hom (P r).hom (hik r) (E₀ r)
  have hlast : ∀ r, (E₁ r).hom ≫ chosenScalarArrow
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) (v r) =
        chosenScalarArrow
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)) (u r) := by
    intro r
    exact mapped_triangle (E₀ r).hom
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (i r).property.2).toRingHom)) (u r))
      (chosenScalarArrow
        (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (i r).property.2).toRingHom)) (v r))
      (extendModelMorphism S (X r).hom (P r).hom (hik r))
      (extendModelMorphism S (P r).hom (D r).hom (hik r))
      (extendModelMorphism S (X r).hom (D r).hom (hik r))
      (E₁ r).hom _ _ rfl (curveModel_extend_arrow S (v r) (hik r))
      (curveModel_extend_arrow S (u r) (hik r))
      (curveModel_extend_composition S (X r).hom (P r).hom (D r).hom (hik r) (E₀ r).hom _).symm
      (hend r)
  exact ⟨E, k, hstart, E₁,
    fun r => extendModelMorphism_baseChange S (X r).hom (P r).hom (hik r)
      (E₀ r).hom (E r).hom (hhom r),
    fun r => extendModelMorphism_baseChange S (P r).hom (X r).hom (hik r)
      (E₀ r).inv (E r).inv (hinv r), hlast,
    fun r => inverse_triangle (E₁ r) _ _ (hlast r)⟩

private def cell_source {B : Scheme.{u}} {Z F C : Over B}
    (f : Z ⟶ F) (c : C ⟶ F) : Over B :=
  Over.mk (pullback.snd f.left c.left ≫ C.hom)

private def cell_source_projection {B : Scheme.{u}} {Z F C : Over B}
    (f : Z ⟶ F) (c : C ⟶ F) : cell_source f c ⟶ C :=
  Over.homMk (pullback.snd f.left c.left) rfl

private def point_fibre {B : Scheme.{u}} {Z F : Over B}
    (f : Z ⟶ F) (b : Over.mk (𝟙 B) ⟶ F) : Over B :=
  Over.mk (pullback.snd f.left b.left)

private theorem point_fibre_properties
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Z F : Over (Spec (.of R))} [CompactSpace Z.left]
    [LocallyOfFinitePresentation Z.hom] [LocallyOfFinitePresentation F.hom]
    (f : Z ⟶ F) (b : Over.mk (𝟙 (Spec (.of R))) ⟶ F) :
    LocallyOfFinitePresentation (point_fibre f b).hom ∧
      CompactSpace (point_fibre f b).left ∧
      QuasiSeparatedSpace (point_fibre f b).left := by
  let : CompactSpace (Over.mk (𝟙 (Spec (.of R)))).left :=
    inferInstanceAs (CompactSpace (Spec (.of R)))
  let : LocallyOfFinitePresentation (Over.mk (𝟙 (Spec (.of R)))).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (𝟙 (Spec (.of R))))
  have h := pullback_model_properties f b
  refine ⟨?_, h.2.1, h.2.2⟩
  change LocallyOfFinitePresentation (pullback.snd f.left b.left)
  exact (Category.comp_id (pullback.snd f.left b.left)) ▸ h.1

/-- The finite family of cell-product comparisons extends with both cell
projection equations to one stage above the specified coefficient stage. -/
theorem exists_bsdh_cell_stages
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K)
    (word : List G.rootBase.support) {J : Type v} [Fintype J] (w : J → G.weylGroup)
    (Z F : Over (Spec (.of S))) [CompactSpace Z.left]
    [LocallyOfFinitePresentation Z.hom] [LocallyOfFinitePresentation F.hom]
    (C : J → Over (Spec (.of S))) [∀ r, CompactSpace (C r).left]
    [∀ r, LocallyOfFinitePresentation (C r).hom]
    (f : Z ⟶ F) (c : ∀ r, C r ⟶ F)
    (b : ∀ _r : J, Over.mk (𝟙 (Spec (.of S))) ⟶ F)
    (qZ : (bsdhVariety G word).scheme ⟶ Z.left)
    (qF : (flagVariety G).scheme ⟶ F.left)
    (qC : ∀ r, (schubertCell G (w r)).scheme ⟶ (C r).left)
    (hZ : IsPullback qZ (bsdhVariety G word).toSpec Z.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hF : IsPullback qF (flagVariety G).toSpec F.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hC : ∀ r, IsPullback (qC r) (schubertCell G (w r)).toSpec (C r).hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (hf : bsdhMap G word ≫ qF = qZ ≫ f.left)
    (hc : ∀ r, (schubertCellInclusion G (w r)).left ≫ qF = qC r ≫ (c r).left)
    (hb : ∀ r, (weylFlagPoint G (w r)).val ≫ qF =
      Spec.map (CommRingCat.ofHom (algebraMap S K)) ≫ (b r).left)
    (start : CoefficientStage S) :
    cell_stage_result S (fun r => cell_source f (c r))
      (fun r => C r ⊗ point_fibre f (b r)) C
      (fun r => cell_source_projection f (c r))
      (fun r => fst (C r) (point_fibre f (b r))) start := by
  let : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).mp hS
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have hX := fun r => pullback_model_properties f (c r)
  have hW := fun r => point_fibre_properties f (b r)
  let (r : J) : LocallyOfFinitePresentation (cell_source f (c r)).hom := (hX r).1
  let (r : J) : CompactSpace (cell_source f (c r)).left := (hX r).2.1
  let (r : J) : QuasiSeparatedSpace (cell_source f (c r)).left := (hX r).2.2
  let (r : J) : LocallyOfFinitePresentation (point_fibre f (b r)).hom := (hW r).1
  let (r : J) : CompactSpace (point_fibre f (b r)).left := (hW r).2.1
  let (r : J) : IsLocallyNoetherian (point_fibre f (b r)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (point_fibre f (b r)).hom
  let (r : J) : AlgebraicGeometry.IsNoetherian (point_fibre f (b r)).left :=
    AlgebraicGeometry.IsNoetherian.mk
  let (r : J) : QuasiCompact (point_fibre f (b r)).hom := inferInstance
  have hP := fun r => product_model_properties (C r) (point_fibre f (b r))
  let (r : J) : LocallyOfFinitePresentation (C r ⊗ point_fibre f (b r)).hom := (hP r).1
  let (r : J) : CompactSpace (C r ⊗ point_fibre f (b r)).left := (hP r).2.1
  let (r : J) : QuasiSeparatedSpace (C r ⊗ point_fibre f (b r)).left := (hP r).2.2
  apply retain_cell_family S hS (fun r => cell_source f (c r))
    (fun r => C r ⊗ point_fibre f (b r)) C
    (fun r => cell_source_projection f (c r))
    (fun r => fst (C r) (point_fibre f (b r))) _ start
  intro r
  apply curveData_elim (bsdhCell_model_product S G word (w r) Z F (C r) f (c r) (b r)
    qZ qF (qC r) hZ hF (hC r) hf (hc r) (hb r))
  intro E hE
  exact ⟨E, scalar_endpoint_eq (Spec.map (CommRingCat.ofHom (algebraMap S K)))
    (X := cell_source f (c r)) (P := C r ⊗ point_fibre f (b r)) (D := C r) E
    (cell_source_projection f (c r)) (fst (C r) (point_fibre f (b r))) hE⟩

-- GAP: C6-STAGE. Identify each retained partial-flag fibre and Schubert
-- intersection with the SAME incidence model's Weyl fibre, including its
-- two projections and simpleCurveCoefficientMap equation. Instantiate
-- exists_simpleCurves_connected with those manufactured comparisons, keep
-- the cell stages by curveFamilyExtendIso at the resulting common stage, and apply
-- the append incidence certificate and endpoint induction on those models.

end SchubertGeometry
