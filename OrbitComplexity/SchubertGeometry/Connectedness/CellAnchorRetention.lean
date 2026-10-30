import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.AffineOriginComparison
import OrbitComplexity.SchubertGeometry.Connectedness.CellContractionScheme

/-! # Arithmetic cell sections and their Richardson anchors -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace SchubertGeometry.CellContraction
universe u
attribute [local instance] coefficientAlgebra

private theorem origin_trans_compare {T : Type*} [Category T] {B : T}
    {X Y Z : Over B} (e : X ≅ Y) (d : Y ≅ Z) {E : X ≅ Z} (hE : E = e ≪≫ d)
    (s : B ⟶ X.left) (t : B ⟶ Y.left) {v : B ⟶ Z.left}
    (hs : s ≫ e.hom.left = t) (hv : v = t ≫ d.hom.left) : s ≫ E.hom.left = v := by
  subst E
  rw [Iso.trans_hom, Over.comp_left, ← Category.assoc, hs, ← hv]

private theorem coefficient_origin_compare {K : Type u} [CommRing K]
    (X : Over (Spec (.of K))) [IsAffine X.left]
    (ε : Γ(X.left, ⊤) →ₐ[K] K) (v : Spec (.of K) ⟶ X.left)
    (hv : v = FrobeniusSplitting.algebraOriginSection ε ≫ X.left.isoSpec.inv) :
    v = FrobeniusSplitting.algebraOriginSection ε ≫ (coefficientIso X).hom.left := by
  rw [coefficientIso_hom_left]
  exact hv

private theorem over_section_inv {T : Type*} [Category T] {B : T} {X Y : Over B}
    (e : X ≅ Y) {s : B ⟶ X.left} {t : B ⟶ Y.left}
    (h : s ≫ e.hom.left = t) : s = t ≫ e.inv.left := by
  have hi : e.hom.left ≫ e.inv.left = 𝟙 X.left := by
    simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left e.hom_inv_id
  have he := congrArg (fun f => f ≫ e.inv.left) h
  simpa only [Category.assoc, hi, Category.comp_id] using he

private theorem stage_transport {T : Type*} [Category T] {B B₀ Z : T} {X Y : Over B}
    (e : X ≅ Y) {s : B ⟶ X.left} {t : B ⟶ Y.left} (hs : s ≫ e.hom.left = t)
    (κ : B ⟶ B₀) (s₀ : B₀ ⟶ Z) (q : X.left ⟶ Z)
    (hstage : κ ≫ s₀ = s ≫ q) : κ ≫ s₀ = t ≫ e.inv.left ≫ q := by
  rw [over_section_inv e hs, Category.assoc] at hstage
  exact hstage

private theorem anchor_from_section {T : Type*} [Category T] {B B₀ X A Y D : T}
    (κ : B ⟶ B₀) (s₀ : B₀ ⟶ A) (s : B ⟶ X)
    (qX : X ⟶ A) (f : A ⟶ D) (p : X ⟶ Y) (qY : Y ⟶ D)
    (anchor : B ⟶ Y) (ha : anchor = s ≫ p)
    (hs : κ ≫ s₀ = s ≫ qX) (hf : qX ≫ f = p ≫ qY) :
    κ ≫ s₀ ≫ f = anchor ≫ qY := by
  rw [ha, ← Category.assoc, hs, Category.assoc, hf, ← Category.assoc]

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K) {R : Subalgebra ℤ K}

/-- The scalar augmentation defines the section of the arithmetic cell model. -/
def cellArithmeticOrigin (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : FrobeniusSplitting.ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne)) :
    Spec (.of R) ⟶ Spec (.of M.model) :=
  FrobeniusSplitting.algebraOriginSection M.origin

/-- The arithmetic origin is a section of its scalar structure map. -/
theorem cellArithmeticOrigin_base (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : FrobeniusSplitting.ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne)) :
    cellArithmeticOrigin G a b w hne M ≫ cellArithmeticBase G a b w hne M = 𝟙 _ :=
  FrobeniusSplitting.algebraOriginSection_base M.origin

/-- The arithmetic origin has the original cell origin as its generic comparison. -/
theorem cellArithmeticOrigin_comparison (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : FrobeniusSplitting.ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne)) :
    FrobeniusSplitting.genericOriginSection R (cellArithmeticBase G a b w hne M)
        (cellArithmeticOrigin G a b w hne M) (cellArithmeticOrigin_base G a b w hne M) ≫
        (cellArithmeticGenericIso G a b w hne M).hom.left = cellOrigin G a b w hne := by
  have he : ∀ c : M.model, M.comparison ((1 : K) ⊗ₜ[R] c) = M.model.val c := by
    intro c
    simpa only [map_one, one_mul, Subalgebra.val_apply] using M.comparison_tmul (1 : K) c
  have hε : ∀ c : M.model, algebraMap R K (M.origin c) =
      cellOriginAlg G a b w hne (M.model.val c) := by
    intro c
    simpa only [Subalgebra.val_apply] using M.origin_native c
  exact origin_trans_compare (tensorModelOverIso M.comparison)
    (coefficientIso (cellIntersection G a b w))
    (E := cellArithmeticGenericIso G a b w hne M) rfl _ _
    (affineOriginSection_comparison R M.comparison M.model.val he M.origin
      (cellOriginAlg G a b w hne) hε)
    (coefficient_origin_compare (cellIntersection G a b w) (cellOriginAlg G a b w hne)
      (cellOrigin G a b w hne) rfl)

/-- The specified origin section on each finite scalar stage of the cell model. -/
def cellArithmeticStageOrigin (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : FrobeniusSplitting.ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne))
    (i : FrobeniusSplitting.CoefficientStage R) :
    Spec (.of i.val) ⟶
      (FrobeniusSplitting.stageScalarModel R (cellArithmeticBase G a b w hne M) i).left :=
  FrobeniusSplitting.stageOriginSection R (cellArithmeticBase G a b w hne M)
    (cellArithmeticOrigin G a b w hne M) (cellArithmeticOrigin_base G a b w hne M) i

/-- Each finite-stage origin remains a section of the stage structure map. -/
theorem cellArithmeticStageOrigin_base (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : FrobeniusSplitting.ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne))
    (i : FrobeniusSplitting.CoefficientStage R) :
    cellArithmeticStageOrigin G a b w hne M i ≫
      (FrobeniusSplitting.stageScalarModel R (cellArithmeticBase G a b w hne M) i).hom = 𝟙 _ :=
  FrobeniusSplitting.stageOriginSection_base R (cellArithmeticBase G a b w hne M)
    (cellArithmeticOrigin G a b w hne M) (cellArithmeticOrigin_base G a b w hne M) i

/-- The finite-stage section retains the original cell origin through the scalar cone. -/
theorem cellArithmeticStageOrigin_comparison (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : FrobeniusSplitting.ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne))
    (i : FrobeniusSplitting.CoefficientStage R) :
    Spec.map (CommRingCat.ofHom (algebraMap i.val K)) ≫ cellArithmeticStageOrigin G a b w hne M i =
      cellOrigin G a b w hne ≫ (cellArithmeticGenericIso G a b w hne M).inv.left ≫
        (FrobeniusSplitting.modelScalarCone R (cellArithmeticBase G a b w hne M)).π.app (op i) :=
  stage_transport (cellArithmeticGenericIso G a b w hne M)
    (cellArithmeticOrigin_comparison G a b w hne M) _ _ _
    (FrobeniusSplitting.stageOriginSection_comparison R (cellArithmeticBase G a b w hne M)
      (cellArithmeticOrigin G a b w hne M) (cellArithmeticOrigin_base G a b w hne M) i)

/-- A retained cell map carries its origin to the same Richardson anchor. -/
theorem cellArithmeticStageAnchor_comparison (a b w : G.weylGroup)
    (hne : Nonempty (cellIntersection G a b w).left)
    (M : FrobeniusSplitting.ArithmeticContractionModel (R := R)
      (cellContractionAlg G a b w) (cellOriginAlg G a b w hne))
    {D : Scheme.{u}} (d : D ⟶ Spec (.of R))
    (i : FrobeniusSplitting.CoefficientStage R)
    (f : FrobeniusSplitting.stageScalarModel R (cellArithmeticBase G a b w hne M) i ⟶
      FrobeniusSplitting.stageScalarModel R d i)
    (qD : (richardsonVariety G a b).scheme ⟶ (FrobeniusSplitting.stageScalarModel R d i).left)
    (hf : ((cellArithmeticGenericIso G a b w hne M).inv.left ≫
        (FrobeniusSplitting.modelScalarCone R (cellArithmeticBase G a b w hne M)).π.app (op i)) ≫
      f.left = (pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b)).left ≫ qD) :
    Spec.map (CommRingCat.ofHom (algebraMap i.val K)) ≫
        cellArithmeticStageOrigin G a b w hne M i ≫ f.left =
      cellRichardsonAnchor G a b w hne ≫ qD :=
  anchor_from_section _ _ (cellOrigin G a b w hne) _ f.left
    (pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b)).left qD
    (cellRichardsonAnchor G a b w hne) rfl
    (cellArithmeticStageOrigin_comparison G a b w hne M i) hf

end SchubertGeometry.CellContraction
