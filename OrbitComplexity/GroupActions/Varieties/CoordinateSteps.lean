import OrbitComplexity.GroupActions.Varieties.CoordinateCharts

/-! # Steps in coordinate basic opens

Adjoining one coordinate gives a product with the additive line or its nonzero-parameter open.
These charts and coordinate reindexing preserve the coordinate functions and projections.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct
noncomputable section
universe u
namespace GroupActions
variable (K : Type u) [Field K] {κ : Type u} [Finite κ] [IsAlgClosed K]

/-- An unrestricted extra coordinate splits off as an additive-line factor. -/
def coordinateStepIso (S : Finset κ) :
    ((affineSpaceVariety K (κ ⊕ PUnit.{u+1})).openSubvariety
      (coordinateOpen K (coordinateStepInl S))).toOver ≅
        ((affineSpaceVariety K κ).openSubvariety (coordinateOpen K S)).toOver ⊗
          (additiveVariety K).toOver :=
  Variety.openProductIso (affineSpaceVariety K κ) (additiveVariety K)
    (affineSpaceVariety K (κ ⊕ PUnit.{u+1})) (splitAffineIso K)
    (coordinateOpen K S) ⊤ (coordinateOpen K (coordinateStepInl S)) (splitOpen_mem K S) ≪≫
      tensorIso (Iso.refl _) (openTopIso K (additiveVariety K))

/-- An invertible extra coordinate splits off as a punctured-line factor. -/
def coordinateUnitStepIso (S : Finset κ) :
    ((affineSpaceVariety K (κ ⊕ PUnit.{u+1})).openSubvariety
      (coordinateOpen K (coordinateStepUnit S))).toOver ≅
        ((affineSpaceVariety K κ).openSubvariety (coordinateOpen K S)).toOver ⊗
          ((additiveVariety K).openSubvariety (additiveNonzero K)).toOver :=
  Variety.openProductIso (affineSpaceVariety K κ) (additiveVariety K)
    (affineSpaceVariety K (κ ⊕ PUnit.{u+1})) (splitAffineIso K)
    (coordinateOpen K S) (additiveNonzero K) (coordinateOpen K (coordinateStepUnit S))
    (splitUnitOpen_mem K S)

private theorem coordinateStepIso_hom (S : Finset κ) :
    (coordinateStepIso K S).hom =
      (Variety.openProductIso (affineSpaceVariety K κ) (additiveVariety K)
        (affineSpaceVariety K (κ ⊕ PUnit.{u+1})) (splitAffineIso K)
        (coordinateOpen K S) ⊤ (coordinateOpen K (coordinateStepInl S)) (splitOpen_mem K S)).hom ≫
      (𝟙 (((affineSpaceVariety K κ).openSubvariety (coordinateOpen K S)).toOver) ⊗ₘ
        (openTopIso K (additiveVariety K)).hom) := rfl

/-- The coordinate-step chart preserves forgetting and the last coordinate. -/
theorem coordinateStepIso_projections (S : Finset κ) :
    let A := (affineSpaceVariety K κ).openSubvariety (coordinateOpen K S)
    ((coordinateStepIso K S).hom ≫ fst A.toOver (additiveVariety K).toOver ≫
      (affineSpaceVariety K κ).openInclusion (coordinateOpen K S) =
        (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
          (coordinateOpen K (coordinateStepInl S)) ≫ affineMorphism (MvPolynomial.rename Sum.inl)) ∧
    ((coordinateStepIso K S).hom ≫ snd A.toOver (additiveVariety K).toOver =
        (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
          (coordinateOpen K (coordinateStepInl S)) ≫ affineMorphism (coordinateLastMap K)) := by
  dsimp only
  constructor
  · rw [coordinateStepIso_hom]
    simp only [Category.assoc, tensorHom_fst_assoc, Category.id_comp]
    exact (Variety.openProductIso_first (affineSpaceVariety K κ) (additiveVariety K)
      (affineSpaceVariety K (κ ⊕ PUnit.{u+1})) (splitAffineIso K)
      (coordinateOpen K S) ⊤ (coordinateOpen K (coordinateStepInl S)) (splitOpen_mem K S)).trans
        (congrArg (fun f => (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
          (coordinateOpen K (coordinateStepInl S)) ≫ f) (splitAffineIso_first K))
  · rw [coordinateStepIso_hom]
    simp only [Category.assoc, tensorHom_snd]
    change (Variety.openProductIso (affineSpaceVariety K κ) (additiveVariety K)
      (affineSpaceVariety K (κ ⊕ PUnit.{u+1})) (splitAffineIso K)
      (coordinateOpen K S) ⊤ (coordinateOpen K (coordinateStepInl S)) (splitOpen_mem K S)).hom ≫
        snd _ _ ≫ (additiveVariety K).openInclusion ⊤ = _
    exact (Variety.openProductIso_last (affineSpaceVariety K κ) (additiveVariety K)
      (affineSpaceVariety K (κ ⊕ PUnit.{u+1})) (splitAffineIso K)
      (coordinateOpen K S) ⊤ (coordinateOpen K (coordinateStepInl S)) (splitOpen_mem K S)).trans
        (congrArg (fun f => (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
          (coordinateOpen K (coordinateStepInl S)) ≫ f) (splitAffineIso_last K))

/-- The invertible coordinate-step chart preserves both projections. -/
theorem coordinateUnitStepIso_projections (S : Finset κ) :
    let A := (affineSpaceVariety K κ).openSubvariety (coordinateOpen K S)
    let B := (additiveVariety K).openSubvariety (additiveNonzero K)
    ((coordinateUnitStepIso K S).hom ≫ fst A.toOver B.toOver ≫
      (affineSpaceVariety K κ).openInclusion (coordinateOpen K S) =
        (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
          (coordinateOpen K (coordinateStepUnit S)) ≫
            affineMorphism (MvPolynomial.rename Sum.inl)) ∧
    ((coordinateUnitStepIso K S).hom ≫ snd A.toOver B.toOver ≫
      (additiveVariety K).openInclusion (additiveNonzero K) =
        (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
          (coordinateOpen K (coordinateStepUnit S)) ≫ affineMorphism (coordinateLastMap K)) := by
  dsimp only
  constructor
  · exact (Variety.openProductIso_first (affineSpaceVariety K κ) (additiveVariety K)
      (affineSpaceVariety K (κ ⊕ PUnit.{u+1})) (splitAffineIso K)
      (coordinateOpen K S) (additiveNonzero K) (coordinateOpen K (coordinateStepUnit S))
      (splitUnitOpen_mem K S)).trans
        (congrArg (fun f => (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
          (coordinateOpen K (coordinateStepUnit S)) ≫ f) (splitAffineIso_first K))
  · exact (Variety.openProductIso_last (affineSpaceVariety K κ) (additiveVariety K)
      (affineSpaceVariety K (κ ⊕ PUnit.{u+1})) (splitAffineIso K)
      (coordinateOpen K S) (additiveNonzero K) (coordinateOpen K (coordinateStepUnit S))
      (splitUnitOpen_mem K S)).trans
        (congrArg (fun f => (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
          (coordinateOpen K (coordinateStepUnit S)) ≫ f) (splitAffineIso_last K))

omit [IsAlgClosed K] in
private theorem coordinate_points {C A B : Variety K}
    (e : C.toOver ≅ A.toOver ⊗ B.toOver)
    (iC : C.toOver ⟶ (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).toOver)
    (iA : A.toOver ⟶ (affineSpaceVariety K κ).toOver)
    (iB : B.toOver ⟶ (additiveVariety K).toOver)
    (hA : e.hom ≫ fst A.toOver B.toOver ≫ iA =
      iC ≫ affineMorphism (MvPolynomial.rename Sum.inl))
    (hB : e.hom ≫ snd A.toOver B.toOver ≫ iB =
      iC ≫ affineMorphism (coordinateLastMap K)) (x : C.points) :
    (∀ j : κ, affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit)
      (Variety.mapPoints iC x) (Sum.inl j) =
        affineSpaceVarietyPointsEquiv K κ
          (Variety.mapPoints (e.hom ≫ fst A.toOver B.toOver ≫ iA) x) j) ∧
    (affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit) (Variety.mapPoints iC x)
      (Sum.inr PUnit.unit) = (additivePointsEquiv K).symm
        (Variety.mapPoints (e.hom ≫ snd A.toOver B.toOver ≫ iB) x)) := by
  constructor
  · intro j
    let f : (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).toOver ⟶
        (affineSpaceVariety K κ).toOver := affineMorphism (MvPolynomial.rename Sum.inl)
    have hp : Variety.mapPoints (e.hom ≫ fst A.toOver B.toOver ≫ iA) x =
        Variety.mapPoints (iC ≫ f) x := congrArg (fun q => Variety.mapPoints q x) hA
    calc
      _ = affineSpaceVarietyPointsEquiv K κ
          (Variety.mapPoints f (Variety.mapPoints iC x)) j :=
        (affineRename_coord K Sum.inl (Variety.mapPoints iC x) j).symm
      _ = affineSpaceVarietyPointsEquiv K κ (Variety.mapPoints (iC ≫ f) x) j :=
        congrArg (fun q => affineSpaceVarietyPointsEquiv K κ q j)
          (Variety.mapPoints_comp iC f x).symm
      _ = _ := congrArg (fun q => affineSpaceVarietyPointsEquiv K κ q j) hp.symm
  · let f : (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).toOver ⟶
        (additiveVariety K).toOver := affineMorphism (coordinateLastMap K)
    have hp : Variety.mapPoints (e.hom ≫ snd A.toOver B.toOver ≫ iB) x =
        Variety.mapPoints (iC ≫ f) x := congrArg (fun q => Variety.mapPoints q x) hB
    calc
      _ = (additivePointsEquiv K).symm (Variety.mapPoints f (Variety.mapPoints iC x)) :=
        (lastCoordinate_points K (Variety.mapPoints iC x)).symm
      _ = (additivePointsEquiv K).symm (Variety.mapPoints (iC ≫ f) x) :=
        congrArg (additivePointsEquiv K).symm (Variety.mapPoints_comp iC f x).symm
      _ = _ := congrArg (additivePointsEquiv K).symm hp.symm

/-- The additive-line split preserves the preceding and last point coordinates. -/
theorem coordinateStepIso_points (S : Finset κ)
    (x : ((affineSpaceVariety K (κ ⊕ PUnit.{u+1})).openSubvariety
      (coordinateOpen K (coordinateStepInl S))).points) :
    let A := (affineSpaceVariety K κ).openSubvariety (coordinateOpen K S)
    let iC := (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
      (coordinateOpen K (coordinateStepInl S))
    (∀ j : κ, affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit)
      (Variety.mapPoints iC x) (Sum.inl j) =
        affineSpaceVarietyPointsEquiv K κ (Variety.mapPoints
          ((coordinateStepIso K S).hom ≫ fst A.toOver (additiveVariety K).toOver ≫
            (affineSpaceVariety K κ).openInclusion (coordinateOpen K S)) x) j) ∧
    (affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit) (Variety.mapPoints iC x)
      (Sum.inr PUnit.unit) = (additivePointsEquiv K).symm
        (Variety.mapPoints ((coordinateStepIso K S).hom ≫
          snd A.toOver (additiveVariety K).toOver) x)) := by
  dsimp only
  have h := coordinateStepIso_projections K S
  have hB : (coordinateStepIso K S).hom ≫
      snd (((affineSpaceVariety K κ).openSubvariety (coordinateOpen K S)).toOver)
        (additiveVariety K).toOver ≫ 𝟙 (additiveVariety K).toOver =
          (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
            (coordinateOpen K (coordinateStepInl S)) ≫ affineMorphism (coordinateLastMap K) :=
    (Category.comp_id _).trans h.2
  have hc := coordinate_points K (coordinateStepIso K S)
    ((affineSpaceVariety K (κ ⊕ PUnit)).openInclusion (coordinateOpen K (coordinateStepInl S)))
    ((affineSpaceVariety K κ).openInclusion (coordinateOpen K S)) (𝟙 _) h.1 hB x
  simpa only [Category.comp_id] using hc

/-- The punctured-line split preserves the preceding and last point coordinates. -/
theorem coordinateUnitStepIso_points (S : Finset κ)
    (x : ((affineSpaceVariety K (κ ⊕ PUnit.{u+1})).openSubvariety
      (coordinateOpen K (coordinateStepUnit S))).points) :
    let A := (affineSpaceVariety K κ).openSubvariety (coordinateOpen K S)
    let B := (additiveVariety K).openSubvariety (additiveNonzero K)
    let iC := (affineSpaceVariety K (κ ⊕ PUnit)).openInclusion
      (coordinateOpen K (coordinateStepUnit S))
    (∀ j : κ, affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit)
      (Variety.mapPoints iC x) (Sum.inl j) =
        affineSpaceVarietyPointsEquiv K κ (Variety.mapPoints
          ((coordinateUnitStepIso K S).hom ≫ fst A.toOver B.toOver ≫
            (affineSpaceVariety K κ).openInclusion (coordinateOpen K S)) x) j) ∧
    (affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit) (Variety.mapPoints iC x)
      (Sum.inr PUnit.unit) = (additivePointsEquiv K).symm
        (Variety.mapPoints ((coordinateUnitStepIso K S).hom ≫ snd A.toOver B.toOver ≫
          (additiveVariety K).openInclusion (additiveNonzero K)) x)) := by
  exact coordinate_points K (coordinateUnitStepIso K S)
    ((affineSpaceVariety K (κ ⊕ PUnit)).openInclusion (coordinateOpen K (coordinateStepUnit S)))
    ((affineSpaceVariety K κ).openInclusion (coordinateOpen K S))
    ((additiveVariety K).openInclusion (additiveNonzero K))
    (coordinateUnitStepIso_projections K S).1 (coordinateUnitStepIso_projections K S).2 x

end GroupActions

namespace GroupActions
variable (K : Type u) [Field K] {ι κ : Type u} [Finite ι] [Finite κ]

private def reindexAffineIso (e : ι ≃ κ) :
    (affineSpaceVariety K ι).toOver ≅ (affineSpaceVariety K κ).toOver :=
  (algSpec (CommRingCat.of K)).mapIso (CommAlgCat.isoMk
    (MvPolynomial.renameEquiv K e.symm)).op

omit [Finite ι] [Finite κ] in
private theorem reindex_polynomial (e : ι ≃ κ) (S : Finset ι) (T : Finset κ)
    (h : S.map e.toEmbedding = T) :
    MvPolynomial.rename e.symm (∏ j ∈ T, (MvPolynomial.X j : MvPolynomial κ K)) =
      ∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι K) := by
  rw [← h]
  simp only [Finset.prod_map, Equiv.toEmbedding_apply, map_prod, MvPolynomial.rename_X,
    Equiv.symm_apply_apply]

private theorem reindex_preimage (e : ι ≃ κ) (S : Finset ι) (T : Finset κ)
    (h : S.map e.toEmbedding = T) :
    (reindexAffineIso K e).hom.left ⁻¹ᵁ coordinateOpen K T = coordinateOpen K S := by
  apply TopologicalSpace.Opens.ext
  ext x
  change MvPolynomial.rename e.symm (∏ j ∈ T, (MvPolynomial.X j : MvPolynomial κ K)) ∉
      x.asIdeal ↔ (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial ι K)) ∉ x.asIdeal
  rw [reindex_polynomial K e S T h]

private def reindexSchemeIso (e : ι ≃ κ) (S : Finset ι) (T : Finset κ)
    (h : S.map e.toEmbedding = T) :
    (coordinateOpen K S).toScheme ≅ (coordinateOpen K T).toScheme :=
  (affineSpaceVariety K ι).scheme.isoOfEq (reindex_preimage K e S T h).symm ≪≫
    (reindexAffineIso K e).hom.left.preimageIso (coordinateOpen K T)

private theorem reindexSchemeIso_inclusion (e : ι ≃ κ) (S : Finset ι) (T : Finset κ)
    (h : S.map e.toEmbedding = T) :
    (reindexSchemeIso K e S T h).hom ≫ (coordinateOpen K T).ι =
      (coordinateOpen K S).ι ≫ (reindexAffineIso K e).hom.left := by
  rw [reindexSchemeIso, Iso.trans_hom, Category.assoc,
    Scheme.Hom.preimageIso_hom_ι, ← Category.assoc]
  exact congrArg (fun q => q ≫ (reindexAffineIso K e).hom.left)
    (Scheme.isoOfEq_hom_ι (affineSpaceVariety K ι).scheme
      (reindex_preimage K e S T h).symm)

/-- Reindexing coordinates identifies basic opens with corresponding selected sets. -/
def coordinateReindexIso (e : ι ≃ κ) (S : Finset ι) (T : Finset κ)
    (h : S.map e.toEmbedding = T) :
    ((affineSpaceVariety K ι).openSubvariety (coordinateOpen K S)).toOver ≅
      ((affineSpaceVariety K κ).openSubvariety (coordinateOpen K T)).toOver :=
  Over.isoMk (reindexSchemeIso K e S T h) (by
    change (reindexSchemeIso K e S T h).hom ≫
      ((coordinateOpen K T).ι ≫ (affineSpaceVariety K κ).toSpec) =
        (coordinateOpen K S).ι ≫ (affineSpaceVariety K ι).toSpec
    rw [← Category.assoc, reindexSchemeIso_inclusion, Category.assoc]
    exact congrArg (fun q => (coordinateOpen K S).ι ≫ q) (reindexAffineIso K e).hom.w)

/-- The reindexed open chart commutes with the ambient renaming morphism. -/
theorem coordinateReindexIso_inclusion (e : ι ≃ κ) (S : Finset ι) (T : Finset κ)
    (h : S.map e.toEmbedding = T) :
    (coordinateReindexIso K e S T h).hom ≫
      (affineSpaceVariety K κ).openInclusion (coordinateOpen K T) =
        (affineSpaceVariety K ι).openInclusion (coordinateOpen K S) ≫
          affineMorphism (MvPolynomial.rename e.symm) := by
  apply Over.OverMorphism.ext
  exact reindexSchemeIso_inclusion K e S T h


private theorem reindex_affine_coord (f : κ → ι)
    (x : (affineSpaceVariety K ι).points) (j : κ) :
    affineSpaceVarietyPointsEquiv K κ (Variety.mapPoints
      (affineMorphism (MvPolynomial.rename f)) x) j =
        affineSpaceVarietyPointsEquiv K ι x (f j) := by
  obtain ⟨p, rfl⟩ := (affineVarietyPointsEquiv K (MvPolynomial ι K)).symm.surjective x
  change (affineVarietyPointsEquiv K (MvPolynomial κ K)
    (Variety.mapPoints (affineMorphism (MvPolynomial.rename f))
      ((affineVarietyPointsEquiv K (MvPolynomial ι K)).symm p))) (MvPolynomial.X j) =
    ((affineVarietyPointsEquiv K (MvPolynomial ι K))
      ((affineVarietyPointsEquiv K (MvPolynomial ι K)).symm p)) (MvPolynomial.X (f j))
  rw [affineMorphism_points, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact congrArg p (MvPolynomial.rename_X f j)

/-- The reindexing chart evaluates a target coordinate at its inverse index. -/
theorem coordinateReindexIso_points (e : ι ≃ κ) (S : Finset ι) (T : Finset κ)
    (h : S.map e.toEmbedding = T)
    (x : ((affineSpaceVariety K ι).openSubvariety (coordinateOpen K S)).points) (j : κ) :
    affineSpaceVarietyPointsEquiv K κ (Variety.mapPoints
      ((coordinateReindexIso K e S T h).hom ≫
        (affineSpaceVariety K κ).openInclusion (coordinateOpen K T)) x) j =
      affineSpaceVarietyPointsEquiv K ι (Variety.mapPoints
        ((affineSpaceVariety K ι).openInclusion (coordinateOpen K S)) x) (e.symm j) := by
  let f : (affineSpaceVariety K ι).toOver ⟶ (affineSpaceVariety K κ).toOver :=
    affineMorphism (MvPolynomial.rename e.symm)
  let i := (affineSpaceVariety K ι).openInclusion (coordinateOpen K S)
  have hp : Variety.mapPoints ((coordinateReindexIso K e S T h).hom ≫
      (affineSpaceVariety K κ).openInclusion (coordinateOpen K T)) x =
        Variety.mapPoints (i ≫ f) x :=
    congrArg (fun q => Variety.mapPoints q x) (coordinateReindexIso_inclusion K e S T h)
  calc
    _ = affineSpaceVarietyPointsEquiv K κ (Variety.mapPoints (i ≫ f) x) j :=
      congrArg (fun q => affineSpaceVarietyPointsEquiv K κ q j) hp
    _ = affineSpaceVarietyPointsEquiv K κ (Variety.mapPoints f (Variety.mapPoints i x)) j :=
      congrArg (fun q => affineSpaceVarietyPointsEquiv K κ q j) (Variety.mapPoints_comp i f x)
    _ = _ := reindex_affine_coord K e.symm (Variety.mapPoints i x) j

end GroupActions
