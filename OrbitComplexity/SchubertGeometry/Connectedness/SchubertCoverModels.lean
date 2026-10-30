import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Normality.Cells.SchubertCellCover
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.ModelStageCartesian
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.RetainedCovers
import OrbitComplexity.SchubertGeometry.Connectedness.ChosenPairedRetention

set_option autoImplicit false

/-! # Schubert cell covers over a common coefficient stage

The polynomial cell models and the specified Schubert target are extended to
one coefficient stage. Their Cartesian comparisons preserve both the cell
inclusions and the image cover after every further coefficient extension.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReductiveGroups
open FrobeniusSplitting Opposite

namespace SchubertGeometry

universe u v

private theorem bind_exists {A : Sort*} {P : A → Prop} {Q : Prop}
    (h : ∃ a, P a) (f : ∀ a, P a → Q) : Q := by
  obtain ⟨a, ha⟩ := h
  exact f a ha

private theorem replace_leg {T : Type*} [Category T] {X A Y Z : T}
    (q q' : X ⟶ A) (hq : q = q') (f : A ⟶ Z) (j : X ⟶ Y) (p : Y ⟶ Z)
    (h : q ≫ f = j ≫ p) : q' ≫ f = j ≫ p := by
  subst q'
  exact h

private theorem cancel_triangle {T : Type*} [Category T]
    {U V X Y A B : T} (E : U ≅ X) (F : V ≅ Y)
    (g : U ⟶ V) (p : X ⟶ A) (q : Y ⟶ B) (f : A ⟶ B)
    (h : (E.hom ≫ p) ≫ f = g ≫ (F.hom ≫ q)) :
    p ≫ f = (E.inv ≫ g ≫ F.hom) ≫ q := by
  calc
    p ≫ f = E.inv ≫ ((E.hom ≫ p) ≫ f) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = E.inv ≫ (g ≫ (F.hom ≫ q)) := congrArg (fun z => E.inv ≫ z) h
    _ = (E.inv ≫ g ≫ F.hom) ≫ q := by simp only [Category.assoc]

private theorem restore_triangle {T : Type*} [Category T]
    {U V X Y A B : T} (E : U ≅ X) (F : V ≅ Y)
    (g : U ⟶ V) (p : X ⟶ A) (q : Y ⟶ B) (f : A ⟶ B)
    (h : p ≫ f = (E.inv ≫ g ≫ F.hom) ≫ q) :
    (E.hom ≫ p) ≫ f = g ≫ (F.hom ≫ q) := by
  calc
    (E.hom ≫ p) ≫ f = E.hom ≫ (p ≫ f) := Category.assoc _ _ _
    _ = E.hom ≫ ((E.inv ≫ g ≫ F.hom) ≫ q) :=
      congrArg (fun z => E.hom ≫ z) h
    _ = g ≫ (F.hom ≫ q) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem map_cartesian {T : Type*} [Category T] {B B' : T}
    {X Y : Over B} {X' Y' : Over B'}
    (κ : B' ⟶ B) (qX : X'.left ⟶ X.left) (qY : Y'.left ⟶ Y.left)
    (hX : IsPullback qX X'.hom X.hom κ)
    (hY : IsPullback qY Y'.hom Y.hom κ)
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : f'.left ≫ qY = qX ≫ f.left) : IsPullback qX f'.left f.left qY := by
  have houter : IsPullback qX (f'.left ≫ Y'.hom) (f.left ≫ Y.hom) κ := by
    rw [f'.w, f.w]
    exact hX
  exact houter.of_bot h.symm hY

private theorem scalar_arrow_cartesian {B T : Scheme.{u}} (κ : T ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) :
    IsPullback (pullback.snd κ X.hom) (chosenScalarArrow κ f).left
      f.left (pullback.snd κ Y.hom) := by
  have hf : (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom =
      pullback.fst κ X.hom := by
    have h := (chosenScalarArrow κ f).w
    change (chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom =
      pullback.fst κ X.hom at h
    exact h
  have h : IsPullback ((chosenScalarArrow κ f).left ≫ pullback.fst κ Y.hom)
      (pullback.snd κ X.hom) κ (f.left ≫ Y.hom) := by
    rw [hf, f.w]
    exact IsPullback.of_hasPullback κ X.hom
  exact (h.of_right (chosenScalarArrow_snd κ f)
    (IsPullback.of_hasPullback κ Y.hom)).flip

private theorem cover_baseChange {I : Type v} {B T : Scheme.{u}} (κ : T ⟶ B)
    (X : I → Over B) (Y : Over B) (f : ∀ i, X i ⟶ Y)
    (hcover : ∀ y : Y.left, ∃ i, y ∈ Set.range (f i).left) :
    ∀ y : (pullback κ Y.hom : Scheme.{u}),
      ∃ i, y ∈ Set.range (chosenScalarArrow κ (f i)).left := by
  intro y
  obtain ⟨i, hi⟩ := hcover ((pullback.snd κ Y.hom) y)
  refine ⟨i, ?_⟩
  exact (Set.ext_iff.mp
    (retainedRange_of_isPullback (scalar_arrow_cartesian κ (f i))) y).mpr hi

private theorem change_raw_cover {I : Type v} {B T : Scheme.{u}}
    (X : I → Scheme.{u}) (Y : Scheme.{u}) (b : Y ⟶ B)
    (f : ∀ i, X i ⟶ Y) (κ κ' : T ⟶ B) (hκ : κ = κ')
    (hcover : ∀ y : (pullback b κ : Scheme.{u}),
      ∃ i, ∃ z : (pullback (f i) (pullback.fst b κ) : Scheme.{u}),
        (pullback.snd (f i) (pullback.fst b κ)) z = y) :
    ∀ y : (pullback b κ' : Scheme.{u}),
      ∃ i, ∃ z : (pullback (f i) (pullback.fst b κ') : Scheme.{u}),
        (pullback.snd (f i) (pullback.fst b κ')) z = y := by
  subst κ'
  exact hcover

private theorem cover_from_raw {I : Type v} {B T : Scheme.{u}}
    (X : I → Over B) (Y : Over B) (X' : I → Over T) (Y' : Over T)
    (f : ∀ i, X i ⟶ Y) (f' : ∀ i, X' i ⟶ Y')
    (κ : T ⟶ B) (qX : ∀ i, (X' i).left ⟶ (X i).left)
    (qY : Y'.left ⟶ Y.left) (hY : IsPullback qY Y'.hom Y.hom κ)
    (hsq : ∀ i, IsPullback (qX i) (f' i).left (f i).left qY)
    (hcover : ∀ y : (pullback Y.hom κ : Scheme.{u}),
      ∃ i, ∃ z : (pullback (f i).left (pullback.fst Y.hom κ) : Scheme.{u}),
        (pullback.snd (f i).left (pullback.fst Y.hom κ)) z = y) :
    ∀ y : Y'.left, ∃ i, y ∈ Set.range (f' i).left := by
  intro y
  let y₀ : (pullback Y.hom κ : Scheme.{u}) := hY.isoPullback.hom y
  obtain ⟨i, z, hz⟩ := hcover y₀
  have hmem : qY y ∈ Set.range (f i).left := by
    refine ⟨(pullback.fst (f i).left (pullback.fst Y.hom κ)) z, ?_⟩
    have hc := congrArg
      (fun m : pullback (f i).left (pullback.fst Y.hom κ) ⟶ Y.left => m z)
      (pullback.condition (f := (f i).left) (g := pullback.fst Y.hom κ))
    change (f i).left ((pullback.fst (f i).left (pullback.fst Y.hom κ)) z) =
      (pullback.fst Y.hom κ)
        ((pullback.snd (f i).left (pullback.fst Y.hom κ)) z) at hc
    calc
      (f i).left ((pullback.fst (f i).left (pullback.fst Y.hom κ)) z) =
          (pullback.fst Y.hom κ) y₀ :=
        hc.trans (congrArg (fun t => (pullback.fst Y.hom κ) t) hz)
      _ = qY y := congrArg (fun m : Y'.left ⟶ Y.left => m y)
        hY.isoPullback_hom_fst
  exact ⟨i, (Set.ext_iff.mp (retainedRange_of_isPullback (hsq i)) y).mpr hmem⟩

private theorem stage_triangle {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {C Y : Over (Spec (.of S))} {U V : Over (Spec (.of K))}
    (E : U ≅ genericScalarModel S C.hom) (F : V ≅ genericScalarModel S Y.hom)
    (g : U ⟶ V) {r R : CoefficientStage S} (hrR : r ≤ R)
    (c : stageScalarModel S C.hom r ⟶ stageScalarModel S Y.hom r)
    (h : (E.hom.left ≫ (modelScalarCone S C.hom).π.app (op r)) ≫ c.left =
      g.left ≫ (F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op r))) :
    (E.hom.left ≫ (modelScalarCone S C.hom).π.app (op R)) ≫
        (extendModelMorphism S C.hom Y.hom hrR c).left =
      g.left ≫ (F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op R)) := by
  let d : genericScalarModel S C.hom ⟶ genericScalarModel S Y.hom :=
    E.inv ≫ g ≫ F.hom
  have hd : (modelScalarCone S C.hom).π.app (op r) ≫ c.left =
      d.left ≫ (modelScalarCone S Y.hom).π.app (op r) :=
    cancel_triangle ((Over.forget _).mapIso E) ((Over.forget _).mapIso F)
      g.left _ _ c.left h
  exact restore_triangle ((Over.forget _).mapIso E) ((Over.forget _).mapIso F)
    g.left _ _ _ (extendModelMorphism_baseChange S C.hom Y.hom hrR c d hd)

private theorem cone_original {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (Y : Over (Spec (.of S))) (R : CoefficientStage S) :
    (modelScalarCone S Y.hom).π.app (op R) ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion R.property.2).toRingHom))
          Y.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) Y.hom := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  exact pullback.lift_snd _ _ _

private theorem stage_original {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (Y : Over (Spec (.of S))) (V : Over (Spec (.of K)))
    (F : V ≅ genericScalarModel S Y.hom) (q : V.left ⟶ Y.left)
    (hq : F.hom.left ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) Y.hom = q)
    (R : CoefficientStage S) :
    (F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op R)) ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion R.property.2).toRingHom))
          Y.hom = q := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => F.hom.left ≫ t) (cone_original S Y R)).trans hq)

private theorem stage_fp {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (C : Over (Spec (.of S))) [LocallyOfFinitePresentation C.hom]
    (R : CoefficientStage S) : LocallyOfFinitePresentation (stageScalarModel S C.hom R).hom := by
  change LocallyOfFinitePresentation (pullback.fst _ C.hom)
  infer_instance

private theorem stage_compact {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    (C : Over (Spec (.of S))) [QuasiCompact C.hom] (R : CoefficientStage S) :
    CompactSpace (stageScalarModel S C.hom R).left := by
  change CompactSpace (pullback _ C.hom : Scheme.{u})
  infer_instance

private def cover_models_result {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} (C : J → Over (Spec (.of S))) (Y : Over (Spec (.of S)))
    (U : J → Over (Spec (.of K))) (V : Over (Spec (.of K)))
    (E : ∀ j, U j ≅ genericScalarModel S (C j).hom)
    (F : V ≅ genericScalarModel S Y.hom) (g : ∀ j, U j ⟶ V)
    (q : V.left ⟶ Y.left) (start : CoefficientStage S) : Prop :=
  ∃ (R : CoefficientStage S), start ≤ R ∧
    ∃ (c : ∀ j, stageScalarModel S (C j).hom R ⟶ stageScalarModel S Y.hom R),
      (∀ j, CompactSpace (stageScalarModel S (C j).hom R).left) ∧
      (∀ j, LocallyOfFinitePresentation (stageScalarModel S (C j).hom R).hom) ∧
      (∀ j, IsPullback
        ((E j).hom.left ≫ (modelScalarCone S (C j).hom).π.app (op R))
        (U j).hom (stageScalarModel S (C j).hom R).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R.val K)))) ∧
      IsPullback (F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op R))
        V.hom (stageScalarModel S Y.hom R).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R.val K))) ∧
      ((F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op R)) ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion R.property.2).toRingHom))
          Y.hom = q) ∧
      (∀ j, ((E j).hom.left ≫ (modelScalarCone S (C j).hom).π.app (op R)) ≫
          (c j).left = (g j).left ≫
            (F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op R))) ∧
      ∀ (k : CoefficientStage R.val),
        let κ := Spec.map
          (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
        ∀ y : (stageScalarModel R.val (stageScalarModel S Y.hom R).hom k).left,
          ∃ j, y ∈ Set.range (chosenScalarArrow κ (c j)).left

private theorem refine_cover_models {K : Type u} [CommRing K] (S : Subalgebra ℤ K)
    {J : Type v} (C : J → Over (Spec (.of S)))
    [∀ j, LocallyOfFinitePresentation (C j).hom] [∀ j, QuasiCompact (C j).hom]
    (Y : Over (Spec (.of S))) (U : J → Over (Spec (.of K)))
    (V : Over (Spec (.of K)))
    (E : ∀ j, U j ≅ genericScalarModel S (C j).hom)
    (F : V ≅ genericScalarModel S Y.hom) (g : ∀ j, U j ⟶ V)
    (q : V.left ⟶ Y.left)
    (hq : F.hom.left ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S K))) Y.hom = q)
    (start r : CoefficientStage S)
    (c : ∀ j, stageScalarModel S (C j).hom r ⟶ stageScalarModel S Y.hom r)
    (hc : ∀ j, ((E j).hom.left ≫ (modelScalarCone S (C j).hom).π.app (op r)) ≫
      (c j).left = (g j).left ≫ (F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op r)))
    (hcover : ∃ (R : Subalgebra ℤ K) (hrR : r.val ≤ R),
      let _ : Algebra r.val R := (Subalgebra.inclusion hrR).toAlgebra
      R.FG ∧ ∀ (T : Type u) [CommRing T] [Algebra R T],
        let _ : Algebra r.val T := ((algebraMap R T).comp (algebraMap r.val R)).toAlgebra
        ∀ y : (pullback (stageScalarModel S Y.hom r).hom
          (Spec.map (CommRingCat.ofHom (algebraMap r.val T))) : Scheme.{u}),
          ∃ j, ∃ z : (pullback (c j).left
            (pullback.fst (stageScalarModel S Y.hom r).hom
              (Spec.map (CommRingCat.ofHom (algebraMap r.val T)))) : Scheme.{u}),
            (pullback.snd (c j).left
              (pullback.fst (stageScalarModel S Y.hom r).hom
                (Spec.map (CommRingCat.ofHom (algebraMap r.val T))))) z = y) :
    cover_models_result S C Y U V E F g q start := by
  obtain ⟨R₀, hrR₀, hR₀⟩ := hcover
  let : Algebra r.val R₀ := (Subalgebra.inclusion hrR₀).toAlgebra
  obtain ⟨hFG, hcoverR₀⟩ := hR₀
  let r₀ : CoefficientStage S := ⟨R₀, hFG, r.property.2.trans hrR₀⟩
  obtain ⟨R, hr₀R, hstart⟩ := exists_ge_ge r₀ start
  have hrR : r ≤ R := hrR₀.trans hr₀R
  let : Algebra R₀ R.val := (Subalgebra.inclusion hr₀R).toAlgebra
  let : Algebra r.val R.val :=
    ((algebraMap R₀ R.val).comp (algebraMap r.val R₀)).toAlgebra
  let κ : Spec (.of R.val) ⟶ Spec (.of r.val) :=
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hrR).toRingHom)
  have hκ : Spec.map (CommRingCat.ofHom (algebraMap r.val R.val)) = κ := by
    apply congrArg (fun f : CommRingCat.of r.val ⟶ CommRingCat.of R.val => Spec.map f)
    ext x
    rfl
  let d (j : J) : stageScalarModel S (C j).hom R ⟶ stageScalarModel S Y.hom R :=
    extendModelMorphism S (C j).hom Y.hom hrR (c j)
  have hsq (j : J) : IsPullback
      (stageScalarTransition S (C j).hom hrR) (d j).left (c j).left
      (stageScalarTransition S Y.hom hrR) :=
    map_cartesian κ _ _ (stageScalarCartesian S (C j).hom hrR)
      (stageScalarCartesian S Y.hom hrR) (c j) (d j)
      (extendModelMorphism_transition S (C j).hom Y.hom hrR (c j))
  have hraw : ∀ y : (pullback (stageScalarModel S Y.hom r).hom κ : Scheme.{u}),
      ∃ j, ∃ z : (pullback (c j).left
        (pullback.fst (stageScalarModel S Y.hom r).hom κ) : Scheme.{u}),
        (pullback.snd (c j).left
          (pullback.fst (stageScalarModel S Y.hom r).hom κ)) z = y :=
    change_raw_cover (fun j => (stageScalarModel S (C j).hom r).left)
      (stageScalarModel S Y.hom r).left (stageScalarModel S Y.hom r).hom
      (fun j => (c j).left) _ κ hκ (hcoverR₀ R.val)
  have hcoverR : ∀ y : (stageScalarModel S Y.hom R).left,
      ∃ j, y ∈ Set.range (d j).left :=
    cover_from_raw (fun j => stageScalarModel S (C j).hom r)
      (stageScalarModel S Y.hom r) (fun j => stageScalarModel S (C j).hom R)
      (stageScalarModel S Y.hom R) c d κ
      (fun j => stageScalarTransition S (C j).hom hrR)
      (stageScalarTransition S Y.hom hrR) (stageScalarCartesian S Y.hom hrR) hsq hraw
  refine ⟨R, hstart, d, (fun j => stage_compact S (C j) R),
    (fun j => stage_fp S (C j) R), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => overIso_modelStage_cartesian S (C j).hom R (U j) (E j)
  · exact overIso_modelStage_cartesian S Y.hom R V F
  · exact stage_original S Y V F q hq R
  · exact fun j => stage_triangle S (E j) F (g j) hrR (c j) (hc j)
  · intro k
    exact cover_baseChange
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom))
      (fun j => stageScalarModel S (C j).hom R) (stageScalarModel S Y.hom R) d hcoverR

private theorem polynomial_fp {R : Type u} [CommRing R] (n : ℕ) :
    LocallyOfFinitePresentation (cellPolynomialModel R n).hom := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  change (algebraMap R (MvPolynomial (Fin n) R)).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  infer_instance

private theorem polynomial_qc {R : Type u} [CommRing R] (n : ℕ) :
    QuasiCompact (cellPolynomialModel R n).hom := by
  change QuasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))
  infer_instance

/-- The polynomial lower-cell cover is retained above a prescribed coefficient
stage, on the same Schubert target and with both scalar comparisons. The cover
continues to hold after every further coefficient extension. -/
theorem exists_schubert_cover_models
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) (G : ReductiveGroupData K) (v : G.weylGroup)
    (Y : Over (Spec (.of S))) [LocallyOfFinitePresentation Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (qY : (schubertVariety G v).scheme ⟶ Y.left)
    (hY : IsPullback qY (schubertVariety G v).toSpec Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap S K)))) (start : CoefficientStage S) :
    let J := {w : G.weylGroup // WeylBruhatLE G.rootBase w v}
    let C (w : J) := cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length w.val)
    let E (w : J) := SchubertGeometry.cellModelIso S G w.val
    let F : (schubertVariety G v).toOver ≅ genericScalarModel S Y.hom :=
      Over.isoMk hY.flip.isoPullback hY.flip.isoPullback_hom_fst
    ∃ (R : CoefficientStage S), start ≤ R ∧
      ∃ (c : ∀ w : J, stageScalarModel S (C w).hom R ⟶ stageScalarModel S Y.hom R),
        (∀ w : J, CompactSpace (stageScalarModel S (C w).hom R).left) ∧
        (∀ w : J, LocallyOfFinitePresentation (stageScalarModel S (C w).hom R).hom) ∧
        (∀ w : J, IsPullback
          ((E w).hom.left ≫ (modelScalarCone S (C w).hom).π.app (op R))
          (schubertCell G w.val).toSpec (stageScalarModel S (C w).hom R).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R.val K)))) ∧
        IsPullback (F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op R))
          (schubertVariety G v).toSpec (stageScalarModel S Y.hom R).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R.val K))) ∧
        ((F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op R)) ≫
          pullback.snd
            (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion R.property.2).toRingHom))
            Y.hom = qY) ∧
        (∀ w : J, ((E w).hom.left ≫ (modelScalarCone S (C w).hom).π.app (op R)) ≫
            (c w).left = (schubertCellOfLE G w.val v w.property).left ≫
              (F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op R))) ∧
        ∀ (k : CoefficientStage R.val),
          let κ := Spec.map
            (CommRingCat.ofHom (Subalgebra.inclusion k.property.2).toRingHom)
          ∀ y : (stageScalarModel R.val (stageScalarModel S Y.hom R).hom k).left,
            ∃ w : J, y ∈ Set.range (chosenScalarArrow κ (c w)).left := by
  let J := {w : G.weylGroup // WeylBruhatLE G.rootBase w v}
  let C (w : J) : Over (Spec (.of S)) :=
    cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length w.val)
  let E (w : J) := SchubertGeometry.cellModelIso S G w.val
  let F : (schubertVariety G v).toOver ≅ genericScalarModel S Y.hom :=
    Over.isoMk hY.flip.isoPullback hY.flip.isoPullback_hom_fst
  let : ∀ w : J, LocallyOfFinitePresentation (C w).hom :=
    fun w => polynomial_fp ((weylCoxeterSystem G.rootBase).length w.val)
  let : ∀ w : J, QuasiCompact (C w).hom :=
    fun w => polynomial_qc ((weylCoxeterSystem G.rootBase).length w.val)
  exact bind_exists (exists_schubert_cell_cover S hS G v Y qY hY) (fun r hr =>
    bind_exists hr (fun c hc =>
      refine_cover_models S C Y (fun w => (schubertCell G w.val).toOver)
        (schubertVariety G v).toOver E F
        (fun w => schubertCellOfLE G w.val v w.property) qY
        hY.flip.isoPullback_hom_snd start r c
        (fun w => replace_leg _ _ rfl (c w).left
          (schubertCellOfLE G w.val v w.property).left
          (F.hom.left ≫ (modelScalarCone S Y.hom).π.app (op r)) (hc.1 w)) hc.2))

end SchubertGeometry
