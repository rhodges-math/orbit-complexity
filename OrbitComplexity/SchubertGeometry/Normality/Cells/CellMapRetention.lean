import OrbitComplexity.FrobeniusSplitting.Normality.Limits.ModelStageMaps
import OrbitComplexity.SchubertGeometry.Cells.CellAffine
import OrbitComplexity.FrobeniusSplitting.Normality.SchemeModels
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Data.Finset.Order

/-! # The finite cell maps into the specified flag model -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroupActions ReductiveGroups
open FrobeniusSplitting Opposite

namespace SchubertGeometry

universe u v

/-- The polynomial model with one coordinate for each position in the cell. -/
def cellPolynomialModel (R : Type u) [CommRing R] (n : ℕ) : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))

/-- The cell and the generic fibre of its polynomial model. -/
def cellModelIso
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (S : Subalgebra ℤ K) (G : ReductiveGroupData K) (w : G.weylGroup) :
    (schubertCell G w).toOver ≅ genericScalarModel S
      (cellPolynomialModel S ((weylCoxeterSystem G.rootBase).length w)).hom :=
  schubertCellAffineIso G w ≪≫ Over.isoMk
    (affineModelIso (MvPolynomial.scalarRTensorAlgEquiv (R := S) (N := K)
      (σ := Fin ((weylCoxeterSystem G.rootBase).length w))))
    (affineModelIso_fst _)

private theorem retainFiniteCellMaps
    {K : Type u} [CommRing K] (S : Subalgebra ℤ K) (hS : S.FG)
    {J : Type v} [Finite J] (C : J → Over (Spec (.of S)))
    [∀ j, CompactSpace (C j).left] [∀ j, QuasiSeparatedSpace (C j).left]
    (F : Over (Spec (.of S))) [LocallyOfFinitePresentation F.hom]
    (g : ∀ j, genericScalarModel S (C j).hom ⟶ genericScalarModel S F.hom) :
    ∃ (r : CoefficientStage S)
      (c : ∀ j, stageScalarModel S (C j).hom r ⟶ stageScalarModel S F.hom r),
      ∀ j, (modelScalarCone S (C j).hom).π.app (op r) ≫ (c j).left =
        (g j).left ≫ (modelScalarCone S F.hom).π.app (op r) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let : Nonempty (CoefficientStage S) := ⟨⟨S, hS, le_rfl⟩⟩
  choose r c hc using fun j => exists_model_morphism S hS (C j).hom F.hom (g j)
  obtain ⟨s, hs⟩ := Finset.exists_le (Finset.univ.image r)
  have hrs (j : J) : r j ≤ s :=
    hs (r j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  refine ⟨s, fun j => extendModelMorphism S (C j).hom F.hom (hrs j) (c j), ?_⟩
  intro j
  exact FrobeniusSplitting.extendModelMorphism_baseChange S (C j).hom F.hom (hrs j) (c j) (g j) (hc
    j)


end SchubertGeometry
