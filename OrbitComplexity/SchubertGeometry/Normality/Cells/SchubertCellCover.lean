import OrbitComplexity.SchubertGeometry.Normality.Cells.CellMapRetention
import OrbitComplexity.FrobeniusSplitting.Normality.Models.ModelSquare
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.PriorCoefficientCover
import OrbitComplexity.SchubertGeometry.Cells.OrbitDecomposition
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The lower-cell cover on the same closed Schubert target -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open FrobeniusSplitting Opposite

namespace SchubertGeometry

universe u v

private theorem iso_cancel_projection {D : Type*} [Category D]
    {A B X Y Z : D} (e : A ≅ B) (t : B ⟶ X) (f : X ⟶ Z)
    (j : A ⟶ Y) (q : Y ⟶ Z) (h : t ≫ f = e.inv ≫ j ≫ q) :
    (e.hom ≫ t) ≫ f = j ≫ q := by
  calc
    (e.hom ≫ t) ≫ f = e.hom ≫ (t ≫ f) := Category.assoc _ _ _
    _ = e.hom ≫ (e.inv ≫ j ≫ q) := congrArg (fun z => e.hom ≫ z) h
    _ = j ≫ q := by simp only [Iso.hom_inv_id_assoc]

private theorem retainMaps
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type v} [Finite J] (C : J → Over (Spec (.of S)))
    [∀ j, CompactSpace (C j).left] [∀ j, QuasiSeparatedSpace (C j).left]
    (Y : Over (Spec (.of S))) [LocallyOfFinitePresentation Y.hom]
    (g : ∀ j, genericScalarModel S (C j).hom ⟶ genericScalarModel S Y.hom) :
    ∃ (r : CoefficientStage S)
      (c : ∀ j, stageScalarModel S (C j).hom r ⟶ stageScalarModel S Y.hom r),
      ∀ j, (modelScalarCone S (C j).hom).π.app (op r) ≫ (c j).left =
        (g j).left ≫ (modelScalarCone S Y.hom).π.app (op r) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  choose r c hc using fun j => exists_model_morphism S hS (C j).hom Y.hom (g j)
  obtain ⟨s, hs⟩ := Finset.exists_le (Finset.univ.image r)
  have hrs (j : J) : r j ≤ s :=
    hs (r j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  refine ⟨s, fun j => extendModelMorphism S (C j).hom Y.hom (hrs j) (c j), ?_⟩
  intro j
  exact FrobeniusSplitting.extendModelMorphism_baseChange S (C j).hom Y.hom (hrs j) (c j) (g j) (hc
    j)

private theorem stageMap_finite
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (r : CoefficientStage S) (X Y : Over (Spec (.of S)))
    [IsAffine X.left] [LocallyOfFinitePresentation X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : stageScalarModel S X.hom r ⟶ stageScalarModel S Y.hom r) :
    LocallyOfFinitePresentation f.left ∧ QuasiCompact f.left := by
  let κ := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom)
  let aX : (pullback κ X.hom : Scheme.{u}) ⟶ Spec (.of r.val) := pullback.fst _ _
  let aY : (pullback κ Y.hom : Scheme.{u}) ⟶ Spec (.of r.val) := pullback.fst _ _
  let : LocallyOfFinitePresentation aX := by dsimp only [aX]; infer_instance
  let : LocallyOfFinitePresentation aY := by dsimp only [aY]; infer_instance
  let : QuasiCompact aY := by dsimp only [aY]; infer_instance
  let : IsSeparated aY := by dsimp only [aY]; infer_instance
  let : IsNoetherianRing r.val := isNoetherianRing_of_fg r.property.1
  let : QuasiSeparatedSpace (pullback κ Y.hom : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated aY
  let : IsLocallyNoetherian (pullback κ Y.hom : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian aY
  let : IsAffine (pullback κ X.hom : Scheme.{u}) := by
    dsimp only [κ]
    infer_instance
  let g : (pullback κ X.hom : Scheme.{u}) ⟶ pullback κ Y.hom := f.left
  have hw : g ≫ aY = aX := f.w
  let : LocallyOfFiniteType (g ≫ aY) := hw.symm ▸ inferInstanceAs (LocallyOfFiniteType aX)
  let : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g aY
  have hfp : LocallyOfFinitePresentation g :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  exact ⟨hfp, inferInstanceAs (QuasiCompact g)⟩

private theorem retainCover
    {K : Type u} [Field K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type v} [Finite J] (C : J → Over (Spec (.of S)))
    [∀ j, IsAffine (C j).left] [∀ j, LocallyOfFinitePresentation (C j).hom]
    (Y : Over (Spec (.of S))) [LocallyOfFinitePresentation Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (XK : J → Over (Spec (.of K))) (YK : Over (Spec (.of K)))
    (eC : ∀ j, XK j ≅ genericScalarModel S (C j).hom)
    (qY : YK.left ⟶ Y.left)
    (hY : IsPullback qY YK.hom Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K))))
    (fK : ∀ j, XK j ⟶ YK) (hcoverK : ∀ y : YK.left, ∃ j x, (fK j).left x = y) :
    let eY : YK ≅ genericScalarModel S Y.hom :=
      Over.isoMk hY.flip.isoPullback hY.flip.isoPullback_hom_fst
    ∃ (r : CoefficientStage S)
      (c : ∀ j, stageScalarModel S (C j).hom r ⟶ stageScalarModel S Y.hom r),
      (∀ j, ((eC j).hom.left ≫ (modelScalarCone S (C j).hom).π.app (op r)) ≫
          (c j).left = (fK j).left ≫
            (eY.hom.left ≫ (modelScalarCone S Y.hom).π.app (op r))) ∧
      ∃ (R : Subalgebra ℤ K) (hrR : r.val ≤ R),
        letI : Algebra r.val R := (Subalgebra.inclusion hrR).toAlgebra
        R.FG ∧ ∀ (T : Type u) [CommRing T] [Algebra R T],
          letI : Algebra r.val T :=
            ((algebraMap R T).comp (algebraMap r.val R)).toAlgebra
          ∀ y : (pullback (stageScalarModel S Y.hom r).hom
              (Spec.map (CommRingCat.ofHom (algebraMap r.val T))) : Scheme.{u}),
            ∃ j, ∃ z : (pullback (c j).left
                (pullback.fst (stageScalarModel S Y.hom r).hom
                  (Spec.map (CommRingCat.ofHom (algebraMap r.val T)))) : Scheme.{u}),
              (pullback.snd (c j).left
                (pullback.fst (stageScalarModel S Y.hom r).hom
                  (Spec.map (CommRingCat.ofHom (algebraMap r.val T))))) z = y := by
  let eY : YK ≅ genericScalarModel S Y.hom :=
    Over.isoMk hY.flip.isoPullback hY.flip.isoPullback_hom_fst
  let g j := (eC j).inv ≫ fK j ≫ eY.hom
  obtain ⟨r, c, hc⟩ := retainMaps S hS C Y g
  let κ := Spec.map (CommRingCat.ofHom (algebraMap S K))
  let κr := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion r.property.2).toRingHom)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap r.val K))
  let Yr : Over (Spec (.of r.val)) := Over.mk (pullback.fst κr Y.hom)
  let Cr (j : J) : Over (Spec (.of r.val)) := Over.mk (pullback.fst κr (C j).hom)
  let cr (j : J) : Cr j ⟶ Yr := c j
  let tY : pullback κ Y.hom ⟶ pullback κr Y.hom :=
    (modelScalarCone S Y.hom).π.app (op r)
  let eYh : YK.left ⟶ pullback κ Y.hom := eY.hom.left
  let : IsIso eYh := inferInstanceAs (IsIso eY.hom.left)
  let qYr : YK.left ⟶ Yr.left := eYh ≫ tY
  let qCr (j : J) : (XK j).left ⟶ (Cr j).left :=
    (eC j).hom.left ≫ (modelScalarCone S (C j).hom).π.app (op r)
  have hcomm (j : J) : qCr j ≫ (cr j).left = (fK j).left ≫ qYr := by
    let E : (XK j).left ≅ pullback κ (C j).hom :=
      (Over.forget (Spec (.of K))).mapIso (eC j)
    let tC : pullback κ (C j).hom ⟶ (Cr j).left :=
      (modelScalarCone S (C j).hom).π.app (op r)
    have hn₀ : tC ≫ (cr j).left =
        (E.inv ≫ (fK j).left ≫ eYh) ≫ tY := hc j
    have hn : tC ≫ (cr j).left = E.inv ≫ (fK j).left ≫ qYr := by
      exact hn₀.trans ((Category.assoc _ _ _).trans
        (congrArg (fun z => E.inv ≫ z) (Category.assoc _ _ _)))
    exact iso_cancel_projection E tC (cr j).left (fK j).left qYr hn
  have heY : IsPullback eYh YK.hom (genericScalarModel S Y.hom).hom
      (𝟙 (Spec (.of K))) :=
    IsPullback.of_horiz_isIso ⟨eY.hom.w.trans (Category.comp_id _).symm⟩
  have hstage : IsPullback tY (genericScalarModel S Y.hom).hom Yr.hom ρ :=
    FrobeniusSplitting.modelScalarCartesian S Y.hom r
  have hqYr : IsPullback qYr YK.hom Yr.hom ρ := by
    have h := heY.paste_horiz hstage
    rw [Category.id_comp] at h
    exact h
  let : LocallyOfFinitePresentation Yr.hom := by
    change LocallyOfFinitePresentation (pullback.fst κr Y.hom)
    infer_instance
  let : QuasiCompact Yr.hom := by change QuasiCompact (pullback.fst κr Y.hom); infer_instance
  let : IsSeparated Yr.hom := by change IsSeparated (pullback.fst κr Y.hom); infer_instance
  let : CompactSpace Yr.left := QuasiCompact.compactSpace_of_compactSpace Yr.hom
  let : QuasiSeparatedSpace Yr.left := quasiSeparatedSpace_of_quasiSeparated Yr.hom
  let : ∀ j, LocallyOfFinitePresentation (cr j).left :=
    fun j => (stageMap_finite S r (C j) Y (c j)).1
  let : ∀ j, QuasiCompact (cr j).left := fun j => (stageMap_finite S r (C j) Y (c j)).2
  obtain ⟨R, hrR, hR, hcoverR⟩ := exists_prior_coefficient_cover r.val r.property.1
    (fun j => (Cr j).left) (fun j => (XK j).left)
    (fun j => (cr j).left) (fun j => (fK j).left)
    Yr.hom qCr qYr YK.hom hqYr hcomm hcoverK
  exact ⟨r, cr, hcomm, R, hrR, hR, hcoverR⟩

private theorem polynomial_model_fp {R : Type u} [CommRing R] (n : ℕ) :
    LocallyOfFinitePresentation (cellPolynomialModel R n).hom := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  change (algebraMap R (MvPolynomial (Fin n) R)).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  infer_instance

private def lowerCellLeg
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K)
    (w : G.weylGroup) (r : CoefficientStage S) :
    (schubertCell G w).scheme ⟶
      (stageScalarModel S
        (cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length w)).hom r).left := by
  let C : Over (Spec (.of S)) :=
    cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length w)
  let E : (schubertCell G w).toOver ≅ genericScalarModel S C.hom :=
    SchubertGeometry.cellModelIso S G w
  let t : (genericScalarModel S C.hom).left ⟶ (stageScalarModel S C.hom r).left :=
    (modelScalarCone S C.hom).π.app (op r)
  exact E.hom.left ≫ t

/-- The lower Bruhat cells cover every later coefficient fibre of the
specified closed Schubert target. The target and all its comparisons are
preserved; the model cover is constructed from the scheme-point cover. -/
theorem exists_schubert_cell_cover
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K) (v : G.weylGroup)
    (Y : Over (Spec (.of S))) [LocallyOfFinitePresentation Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (qY : (schubertVariety G v).scheme ⟶ Y.left)
    (hY : IsPullback qY (schubertVariety G v).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) :
    let J := {w : G.weylGroup // WeylBruhatLE G.rootBase w v}
    let eY : (schubertVariety G v).toOver ≅ genericScalarModel S Y.hom :=
      Over.isoMk hY.flip.isoPullback hY.flip.isoPullback_hom_fst
    let C (w : J) := cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length w.val)
    ∃ (r : CoefficientStage S)
      (c : ∀ w : J, stageScalarModel S (C w).hom r ⟶ stageScalarModel S Y.hom r),
      (∀ w : J, lowerCellLeg S G w.val r ≫ (c w).left =
        (schubertCellOfLE G w.val v w.property).left ≫
          (eY.hom.left ≫ (modelScalarCone S Y.hom).π.app (op r))) ∧
      ∃ (R : Subalgebra ℤ K) (hrR : r.val ≤ R),
        letI : Algebra r.val R := (Subalgebra.inclusion hrR).toAlgebra
        R.FG ∧ ∀ (T : Type u) [CommRing T] [Algebra R T],
          letI : Algebra r.val T :=
            ((algebraMap R T).comp (algebraMap r.val R)).toAlgebra
          ∀ y : (pullback (stageScalarModel S Y.hom r).hom
              (Spec.map (CommRingCat.ofHom (algebraMap r.val T))) : Scheme.{u}),
            ∃ w : J, ∃ z : (pullback (c w).left
                (pullback.fst (stageScalarModel S Y.hom r).hom
                  (Spec.map (CommRingCat.ofHom (algebraMap r.val T)))) : Scheme.{u}),
              (pullback.snd (c w).left
                (pullback.fst (stageScalarModel S Y.hom r).hom
                  (Spec.map (CommRingCat.ofHom (algebraMap r.val T))))) z = y := by
  let J := {w : G.weylGroup // WeylBruhatLE G.rootBase w v}
  let : Finite G.weylGroup := ReductiveGroups.weylGroup_finite G.rootBase
  let C (w : J) : Over (Spec (.of S)) :=
    cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length w.val)
  let : ∀ w, IsAffine (C w).left := fun w => by
    change IsAffine (Spec _)
    infer_instance
  let : ∀ w, LocallyOfFinitePresentation (C w).hom :=
    fun w => polynomial_model_fp ((weylCoxeterSystem G.rootBase).length w.val)
  have hcover : ∀ y : (schubertVariety G v).scheme,
      ∃ w : J, ∃ x, (schubertCellOfLE G w.val v w.property).left x = y := by
    intro y
    obtain ⟨w, ⟨x, hx⟩, _⟩ := schubertLowerCells_partition G v y
    exact ⟨w, x, hx⟩
  exact retainCover S hS C Y (fun w => (schubertCell G w.val).toOver)
    (schubertVariety G v).toOver (fun w => SchubertGeometry.cellModelIso S G w.val)
    qY hY (fun w => schubertCellOfLE G w.val v w.property) hcover


end SchubertGeometry
