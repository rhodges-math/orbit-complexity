import OrbitComplexity.SchubertGeometry.Connectedness.RichardsonPieces
import OrbitComplexity.FrobeniusSplitting.Normality.Covers.FiniteCoverModels

/-!
# Retaining the specified original cell cover on a specified target model

The cover input is proved from the original scheme-point cell decomposition.
The coefficient target and all chart maps are specified, and their specified
original comparison equations are retained. A common principal localization
then makes those same charts cover that target. No connectedness assumption
or equality with an independently chosen family of cell models is used.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SchubertGeometry.CellContraction

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- specified models of the nonempty original cell pieces cover the same chosen
Richardson model after one principal coefficient localization. -/
theorem exists_cell_cover_open (a b : G.weylGroup)
    (R : Subalgebra ℤ K) {D : Scheme.{u}}
    [CompactSpace D] [QuasiSeparatedSpace D]
    (d : D ⟶ Spec (.of R)) [LocallyOfFinitePresentation d] [QuasiCompact d]
    (X : cellPieceIndices G a b → Scheme.{u}) (f : ∀ w : cellPieceIndices G a b, X w ⟶ D)
    [∀ w, LocallyOfFinitePresentation (f w)] [∀ w, QuasiCompact (f w)]
    (qX : ∀ w : cellPieceIndices G a b, (cellIntersection G a b w.val).left ⟶ X w)
    (qD : (richardsonVariety G a b).scheme ⟶ D)
    (hD : IsPullback qD (richardsonVariety G a b).toSpec d
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hcomm : ∀ w : cellPieceIndices G a b, qX w ≫ f w =
      (pullback.snd (schubertCellInclusion G w.val) (richardsonInclusion G a b)).left ≫ qD) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : D, d y ∈ PrimeSpectrum.basicOpen r →
      ∃ w x, f w x = y := by
  let : Finite G.weylGroup := ReductiveGroups.weylGroup_finite G.rootBase
  have hinj : Function.Injective (algebraMap R K) := by
    intro x y h
    exact Subtype.ext h
  apply FrobeniusSplitting.exists_finite_model_cover hinj X
    (fun w => (cellIntersection G a b w.val).left) f
    (fun w => (pullback.snd (schubertCellInclusion G w.val)
      (richardsonInclusion G a b)).left) d qX qD
    (richardsonVariety G a b).toSpec hD hcomm
  intro y
  obtain ⟨w, z, hz⟩ := cellPieceImages_cover G a b y
  exact ⟨w, z, hz⟩

end SchubertGeometry.CellContraction
