import OrbitComplexity.GroupActions.Varieties.AffineTensorProduct
import OrbitComplexity.GroupActions.Varieties.AdditiveVariety
import OrbitComplexity.GroupActions.Varieties.CoordinateOpens
import OrbitComplexity.GroupActions.Varieties.OpenPointLifts
import OrbitComplexity.GroupActions.Varieties.OpenSubvarieties
import OrbitComplexity.GroupActions.Varieties.SmoothProducts
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Charts for coordinate basic opens

Polynomial coordinates split an affine space into its preceding coordinates and an additive
line. Restricting such a chart to matching opens preserves the two projection morphisms.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct
noncomputable section
universe u
namespace GroupActions.Variety
variable {K : Type u} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
private theorem point_in_open (X : GroupActions.Variety K) (U : X.scheme.Opens)
    (x : (X.openSubvariety U).points) :
    X.pointMap (mapPoints (X.openInclusion U) x) ∈ U := by
  have hx : X.pointMap (mapPoints (X.openInclusion U) x) ∈
      Set.range ((X.openInclusion U).left : (X.openSubvariety U).scheme → X.scheme) :=
    ⟨(X.openSubvariety U).pointMap x, rfl⟩
  rwa [X.openInclusion_range] at hx

/-- Restrict a product chart to opens specified by its two projections. -/
def openProductIso (A B C : GroupActions.Variety K) [Smooth A.toSpec]
    (e : C.toOver ≅ A.toOver ⊗ B.toOver) (U : A.scheme.Opens) (V : B.scheme.Opens)
    (W : C.scheme.Opens)
    (h : ∀ x : C.points, C.pointMap x ∈ W ↔
      A.pointMap (mapPoints (e.hom ≫ fst A.toOver B.toOver) x) ∈ U ∧
      B.pointMap (mapPoints (e.hom ≫ snd A.toOver B.toOver) x) ∈ V) :
    (C.openSubvariety W).toOver ≅
      (A.openSubvariety U).toOver ⊗ (B.openSubvariety V).toOver := by
  let iA := A.openInclusion U
  let iB := B.openInclusion V
  let iC := C.openInclusion W
  have : Mono iA := Over.mono_of_mono_left iA
  have : Mono iB := Over.mono_of_mono_left iB
  have : Mono iC := Over.mono_of_mono_left iC
  let fA := e.hom ≫ fst A.toOver B.toOver
  let fB := e.hom ≫ snd A.toOver B.toOver
  have hA : ∀ x : (C.openSubvariety W).points,
      mapPoints (iC ≫ fA) x ∈ Set.range (mapPoints iA) := by
    intro x
    apply exists_mapPoints_eq iA
    rw [A.openInclusion_range, mapPoints_comp]
    exact ((h _).mp (point_in_open C W x)).1
  have hB : ∀ x : (C.openSubvariety W).points,
      mapPoints (iC ≫ fB) x ∈ Set.range (mapPoints iB) := by
    intro x
    apply exists_mapPoints_eq iB
    rw [B.openInclusion_range, mapPoints_comp]
    exact ((h _).mp (point_in_open C W x)).2
  let a := liftOpen (iC ≫ fA) iA hA
  let b := liftOpen (iC ≫ fB) iB hB
  let f := lift a b
  let j := iA ⊗ₘ iB
  have hf : f ≫ j = iC ≫ e.hom := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, j, tensorHom_fst, f, lift_fst_assoc]
      exact liftOpen_comp (iC ≫ fA) iA hA
    · simp only [Category.assoc, j, tensorHom_snd, f, lift_snd_assoc]
      exact liftOpen_comp (iC ≫ fB) iB hB
  have : Smooth (A.openSubvariety U).toSpec := by
    change Smooth (U.ι ≫ A.toSpec)
    infer_instance
  let P := smoothProductVariety (A.openSubvariety U) (B.openSubvariety V)
  let g : P.toOver ⟶ C.toOver := j ≫ e.inv
  have hg : ∀ z : P.points, mapPoints g z ∈ Set.range (mapPoints iC) := by
    intro z
    apply exists_mapPoints_eq iC
    rw [C.openInclusion_range]
    apply (h _).mpr
    constructor
    · have he : g ≫ fA = fst (A.openSubvariety U).toOver
          (B.openSubvariety V).toOver ≫ iA := by
        simp only [g, fA, Category.assoc, Iso.inv_hom_id_assoc, j, tensorHom_fst]
      rw [← mapPoints_comp, he, mapPoints_comp]
      exact point_in_open A U _
    · have he : g ≫ fB = snd (A.openSubvariety U).toOver
          (B.openSubvariety V).toOver ≫ iB := by
        simp only [g, fB, Category.assoc, Iso.inv_hom_id_assoc, j, tensorHom_snd]
      rw [← mapPoints_comp, he, mapPoints_comp]
      exact point_in_open B V _
  let g' := liftOpen g iC hg
  have hg' : g' ≫ iC = g := liftOpen_comp g iC hg
  refine ⟨f, g', ?_, ?_⟩
  · apply (cancel_mono iC).mp
    rw [Category.assoc, hg', ← Category.assoc, hf]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · have he : g' ≫ f ≫ j = j := by
      rw [hf, ← Category.assoc, hg']
      simp only [g, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply CartesianMonoidalCategory.hom_ext
    · apply (cancel_mono iA).mp
      simpa only [Category.assoc, j, tensorHom_fst, Category.id_comp] using
        congrArg (fun q => q ≫ fst A.toOver B.toOver) he
    · apply (cancel_mono iB).mp
      simpa only [Category.assoc, j, tensorHom_snd, Category.id_comp] using
        congrArg (fun q => q ≫ snd A.toOver B.toOver) he

/-- The restricted product chart preserves the first ambient projection. -/
theorem openProductIso_first (A B C : GroupActions.Variety K) [Smooth A.toSpec]
    (e : C.toOver ≅ A.toOver ⊗ B.toOver) (U : A.scheme.Opens) (V : B.scheme.Opens)
    (W : C.scheme.Opens)
    (h : ∀ x : C.points, C.pointMap x ∈ W ↔
      A.pointMap (mapPoints (e.hom ≫ fst A.toOver B.toOver) x) ∈ U ∧
      B.pointMap (mapPoints (e.hom ≫ snd A.toOver B.toOver) x) ∈ V) :
    (openProductIso A B C e U V W h).hom ≫
      fst (A.openSubvariety U).toOver (B.openSubvariety V).toOver ≫
        A.openInclusion U = C.openInclusion W ≫ e.hom ≫ fst A.toOver B.toOver := by
  dsimp only [openProductIso]
  rw [lift_fst_assoc]
  exact liftOpen_comp _ _ _

/-- The restricted product chart preserves the second ambient projection. -/
theorem openProductIso_last (A B C : GroupActions.Variety K) [Smooth A.toSpec]
    (e : C.toOver ≅ A.toOver ⊗ B.toOver) (U : A.scheme.Opens) (V : B.scheme.Opens)
    (W : C.scheme.Opens)
    (h : ∀ x : C.points, C.pointMap x ∈ W ↔
      A.pointMap (mapPoints (e.hom ≫ fst A.toOver B.toOver) x) ∈ U ∧
      B.pointMap (mapPoints (e.hom ≫ snd A.toOver B.toOver) x) ∈ V) :
    (openProductIso A B C e U V W h).hom ≫
      snd (A.openSubvariety U).toOver (B.openSubvariety V).toOver ≫
        B.openInclusion V = C.openInclusion W ≫ e.hom ≫ snd A.toOver B.toOver := by
  dsimp only [openProductIso]
  rw [lift_snd_assoc]
  exact liftOpen_comp _ _ _

end GroupActions.Variety

namespace GroupActions
variable (K : Type u) [Field K] {κ : Type u} [Finite κ]

private def lineCoordinateEquiv : SymmetricAlgebra K K ≃ₐ[K] MvPolynomial PUnit.{u+1} K :=
  (ReductiveGroups.gaPolynomialEquiv K).trans (MvPolynomial.uniqueAlgEquiv K _).symm

private theorem lineCoordinateEquiv_generator :
    lineCoordinateEquiv K (SymmetricAlgebra.ι K K 1) = MvPolynomial.X PUnit.unit := by
  apply (MvPolynomial.uniqueAlgEquiv K PUnit).injective
  simp [lineCoordinateEquiv]

private def splitCoordinateEquiv :
    MvPolynomial κ K ⊗[K] SymmetricAlgebra K K ≃ₐ[K]
      MvPolynomial (κ ⊕ PUnit.{u+1}) K :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : MvPolynomial κ K ≃ₐ[K] _)
    (lineCoordinateEquiv K)).trans (MvPolynomial.tensorEquivSum K κ PUnit K)

private instance splitTensorReduced :
    IsReduced (MvPolynomial κ K ⊗[K] SymmetricAlgebra K K) :=
  isReduced_of_injective (splitCoordinateEquiv K).toRingHom
    (splitCoordinateEquiv K).injective

private instance splitTensorFinite :
    Algebra.FiniteType K (MvPolynomial κ K ⊗[K] SymmetricAlgebra K K) :=
  Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K (MvPolynomial κ K))
    (inferInstance : Algebra.FiniteType (MvPolynomial κ K)
      (MvPolynomial κ K ⊗[K] SymmetricAlgebra K K))

/-- Adjoining one polynomial coordinate gives a product with the additive line. -/
def splitAffineIso : (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).toOver ≅
    (affineSpaceVariety K κ).toOver ⊗ (additiveVariety K).toOver :=
  (algSpec (CommRingCat.of K)).mapIso (CommAlgCat.isoMk (splitCoordinateEquiv K)).op ≪≫
    affineTensorIso K (MvPolynomial κ K) (SymmetricAlgebra K K)

private theorem splitAffineIso_hom : (splitAffineIso (κ := κ) K).hom =
    affineMorphism (splitCoordinateEquiv K).toAlgHom ≫
      (affineTensorIso K (MvPolynomial κ K) (SymmetricAlgebra K K)).hom := rfl

omit [Finite κ] in
private theorem splitCoordinateEquiv_left (j : κ) :
    splitCoordinateEquiv K (MvPolynomial.X j ⊗ₜ[K] 1) = MvPolynomial.X (Sum.inl j) := by
  simp [splitCoordinateEquiv]

omit [Finite κ] in
private theorem splitCoordinateEquiv_right :
    splitCoordinateEquiv (κ := κ) K (1 ⊗ₜ[K] SymmetricAlgebra.ι K K 1) =
      MvPolynomial.X (Sum.inr PUnit.unit) := by
  simp [splitCoordinateEquiv, lineCoordinateEquiv_generator]

private theorem affineMorphism_comp {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]
    [IsReduced A] [IsReduced B] [IsReduced C]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B] [Algebra.FiniteType K C]
    (f : A →ₐ[K] B) (g : C →ₐ[K] A) :
    affineMorphism f ≫ affineMorphism g = affineMorphism (f.comp g) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom g.toRingHom) =
      Spec.map (CommRingCat.ofHom (f.comp g).toRingHom)
  rw [← Spec.map_comp]
  rfl

/-- The first projection of the affine chart forgets the last coordinate. -/
theorem splitAffineIso_first : (splitAffineIso (κ := κ) K).hom ≫
    fst (affineSpaceVariety K κ).toOver (additiveVariety K).toOver =
      affineMorphism (MvPolynomial.rename Sum.inl) := by
  let f : (affineVariety K (MvPolynomial (κ ⊕ PUnit.{u+1}) K)).toOver ⟶
      (affineVariety K (MvPolynomial κ K)).toOver ⊗
        (affineVariety K (SymmetricAlgebra K K)).toOver := (splitAffineIso K).hom
  change f ≫ fst (affineVariety K (MvPolynomial κ K)).toOver
    (affineVariety K (SymmetricAlgebra K K)).toOver = _
  rw [show f = affineMorphism (splitCoordinateEquiv K).toAlgHom ≫
      (affineTensorIso K (MvPolynomial κ K) (SymmetricAlgebra K K)).hom from
        splitAffineIso_hom K, Category.assoc, affineTensorIso_fst,
    affineMorphism_comp]
  congr 1
  ext j
  simp [splitCoordinateEquiv_left]

/-- The additive-line coordinate pulls back to the adjoined polynomial variable. -/
def coordinateLastMap : SymmetricAlgebra K K →ₐ[K]
    MvPolynomial (κ ⊕ PUnit.{u+1}) K :=
  (splitCoordinateEquiv K).toAlgHom.comp Algebra.TensorProduct.includeRight

/-- The second projection of the affine chart is the last-coordinate morphism. -/
theorem splitAffineIso_last : (splitAffineIso (κ := κ) K).hom ≫
    snd (affineSpaceVariety K κ).toOver (additiveVariety K).toOver =
      affineMorphism (coordinateLastMap K) := by
  let f : (affineVariety K (MvPolynomial (κ ⊕ PUnit.{u+1}) K)).toOver ⟶
      (affineVariety K (MvPolynomial κ K)).toOver ⊗
        (affineVariety K (SymmetricAlgebra K K)).toOver := (splitAffineIso K).hom
  change f ≫ snd (affineVariety K (MvPolynomial κ K)).toOver
    (affineVariety K (SymmetricAlgebra K K)).toOver = _
  rw [show f = affineMorphism (splitCoordinateEquiv K).toAlgHom ≫
      (affineTensorIso K (MvPolynomial κ K) (SymmetricAlgebra K K)).hom from
        splitAffineIso_hom K, Category.assoc, affineTensorIso_snd,
    affineMorphism_comp]
  rfl

/-- A coordinate renaming evaluates each coordinate at its renamed index. -/
theorem affineRename_coord {ι : Type u} [Finite ι] (f : κ → ι)
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

omit [Finite κ] in
private theorem lastCoordinateMap_generator :
    coordinateLastMap (κ := κ) K (SymmetricAlgebra.ι K K 1) =
      MvPolynomial.X (Sum.inr PUnit.unit) := splitCoordinateEquiv_right K

private theorem affineBasic_mem {A : Type u} [CommRing A] [Algebra K A]
    [IsReduced A] [Algebra.FiniteType K A] (a : A) (x : (affineVariety K A).points) :
    (affineVariety K A).pointMap x ∈ PrimeSpectrum.basicOpen a ↔
      affineVarietyPointsEquiv K A x a ≠ 0 := by
  obtain ⟨p, rfl⟩ := affinePointsEquiv.surjective x
  rw [show (affineVariety K A).pointMap (affinePointsEquiv p) =
      (⟨RingHom.ker p, RingHom.ker_isPrime p⟩ : PrimeSpectrum A) from
        affinePointsEquiv_prime p]
  change p a ≠ 0 ↔ (affinePointsEquiv.symm (affinePointsEquiv p)) a ≠ 0
  rw [Equiv.symm_apply_apply]

private theorem additive_eval_generator (a : (additiveVariety K).points) :
    affineVarietyPointsEquiv K (SymmetricAlgebra K K) a (SymmetricAlgebra.ι K K 1) =
      (additivePointsEquiv K).symm a := by
  obtain ⟨t, rfl⟩ := (additivePointsEquiv K).surjective a
  rw [Equiv.symm_apply_apply]
  let g := ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := K)).symm
    (Multiplicative.ofAdd t)).ofConv
  have ht : additivePointsEquiv K t = affinePointsEquiv g := rfl
  rw [ht]
  change (affinePointsEquiv.symm (affinePointsEquiv g)) (SymmetricAlgebra.ι K K 1) = t
  rw [Equiv.symm_apply_apply]
  dsimp only [g]
  rw [TauCeti.AdditiveGroup.gaPointsMulEquiv_symm_apply_ι]
  rfl

/-- The last-coordinate morphism evaluates the adjoined polynomial variable. -/
theorem lastCoordinate_points (x : (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).points) :
    (additivePointsEquiv K).symm (Variety.mapPoints
      (affineMorphism (coordinateLastMap K)) x) =
        affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit) x (Sum.inr PUnit.unit) := by
  rw [← additive_eval_generator]
  obtain ⟨p, rfl⟩ := (affineVarietyPointsEquiv K
    (MvPolynomial (κ ⊕ PUnit.{u+1}) K)).symm.surjective x
  rw [affineMorphism_points]
  change (affinePointsEquiv.symm (affinePointsEquiv (p.comp (coordinateLastMap K))))
      (SymmetricAlgebra.ι K K 1) =
    (affinePointsEquiv.symm (affinePointsEquiv p)) (MvPolynomial.X (Sum.inr PUnit.unit))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact congrArg p (lastCoordinateMap_generator K)

/-- The basic open where each selected affine coordinate is nonzero. -/
def coordinateOpen (S : Finset κ) : (affineSpaceVariety K κ).scheme.Opens :=
  PrimeSpectrum.basicOpen (∏ j ∈ S, (MvPolynomial.X j : MvPolynomial κ K))

/-- The old selected coordinates in a space with one adjoined coordinate. -/
def coordinateStepInl (S : Finset κ) : Finset (κ ⊕ PUnit.{u+1}) :=
  S.map ⟨Sum.inl, Sum.inl_injective⟩

/-- The selected coordinates when the adjoined coordinate must be nonzero. -/
def coordinateStepUnit (S : Finset κ) : Finset (κ ⊕ PUnit.{u+1}) := by
  classical
  exact insert (Sum.inr PUnit.unit) (coordinateStepInl S)

/-- The open of the additive group with nonzero canonical parameter. -/
def additiveNonzero : (additiveVariety K).scheme.Opens :=
  PrimeSpectrum.basicOpen (SymmetricAlgebra.ι K K 1)

/-- The open subvariety on the whole space is isomorphic to the variety. -/
def openTopIso (X : Variety K) :
    (X.openSubvariety (⊤ : X.scheme.Opens)).toOver ≅ X.toOver :=
  Over.isoMk X.scheme.topIso (by rfl)

private instance affineSpaceSmooth : Smooth (affineSpaceVariety K κ).toSpec := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial κ K))))
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- The unrestricted coordinate open is detected by the first chart projection. -/
theorem splitOpen_mem (S : Finset κ)
    (x : (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).points) :
    (affineSpaceVariety K (κ ⊕ PUnit)).pointMap x ∈ coordinateOpen K (coordinateStepInl S) ↔
      (affineSpaceVariety K κ).pointMap
        (Variety.mapPoints ((splitAffineIso K).hom ≫
          fst (affineSpaceVariety K κ).toOver (additiveVariety K).toOver) x) ∈
            coordinateOpen K S ∧
      (additiveVariety K).pointMap
        (Variety.mapPoints ((splitAffineIso K).hom ≫
          snd (affineSpaceVariety K κ).toOver (additiveVariety K).toOver) x) ∈
            (⊤ : (additiveVariety K).scheme.Opens) := by
  rw [splitAffineIso_first]
  simp only [TopologicalSpace.Opens.mem_top, and_true]
  have hL := affineBasicOpen_points (coordinateStepInl S) x
  have hR := affineBasicOpen_points S
    (Variety.mapPoints (affineMorphism (MvPolynomial.rename Sum.inl)) x)
  exact hL.trans ((by
    simp only [coordinateStepInl, Finset.forall_mem_map, Function.Embedding.coeFn_mk,
      affineRename_coord] : _ ↔ _).trans hR.symm)

/-- The invertible coordinate open is detected by the two chart projections. -/
theorem splitUnitOpen_mem (S : Finset κ)
    (x : (affineSpaceVariety K (κ ⊕ PUnit.{u+1})).points) :
    (affineSpaceVariety K (κ ⊕ PUnit)).pointMap x ∈ coordinateOpen K (coordinateStepUnit S) ↔
      (affineSpaceVariety K κ).pointMap
        (Variety.mapPoints ((splitAffineIso K).hom ≫
          fst (affineSpaceVariety K κ).toOver (additiveVariety K).toOver) x) ∈
            coordinateOpen K S ∧
      (additiveVariety K).pointMap
        (Variety.mapPoints ((splitAffineIso K).hom ≫
          snd (affineSpaceVariety K κ).toOver (additiveVariety K).toOver) x) ∈
            additiveNonzero K := by
  classical
  rw [splitAffineIso_first, splitAffineIso_last]
  have hL := affineBasicOpen_points (coordinateStepUnit S) x
  have hR := affineBasicOpen_points S
    (Variety.mapPoints (affineMorphism (MvPolynomial.rename Sum.inl)) x)
  have hG := affineBasic_mem K (SymmetricAlgebra.ι K K 1)
    (Variety.mapPoints (affineMorphism (coordinateLastMap K)) x)
  have hG' : (additiveVariety K).pointMap
      (Variety.mapPoints (affineMorphism (coordinateLastMap K)) x) ∈ additiveNonzero K ↔
        affineSpaceVarietyPointsEquiv K (κ ⊕ PUnit) x (Sum.inr PUnit.unit) ≠ 0 := by
    exact hG.trans (by rw [additive_eval_generator, lastCoordinate_points])
  exact hL.trans ((by
    simp only [coordinateStepUnit, Finset.forall_mem_insert, coordinateStepInl,
      Finset.forall_mem_map,
      Function.Embedding.coeFn_mk, affineRename_coord]
    exact and_comm : _ ↔ _).trans (hR.and hG').symm)

end GroupActions
