import Batteries.Tactic.Lint
import OrbitComplexity.FrobeniusSplitting.Normality.Connectedness.PolynomialRetention
import OrbitComplexity.SchubertGeometry.Connectedness.CellConnected
import Mathlib.RingTheory.FinitePresentation

/-!
# Arithmetic retention of the original cell contractions

-/

noncomputable section

namespace SchubertGeometry.CellContraction

universe u

attribute [local instance] coefficientAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

/-- The specified closed cell-intersection coordinates are finitely presented:
they are a quotient of the finite inversion-coordinate polynomial algebra. -/
theorem cellCoefficients_finitePres (a b w : G.weylGroup) :
    Algebra.FinitePresentation K (cellCoefficients G a b w) := by
  have hft : Algebra.FiniteType K (cellCoefficients G a b w) :=
    Algebra.FiniteType.of_surjective (cellIntersectionAlgMap G a b w)
      (cellIntersectionAlgMap_surj G a b w)
  exact Algebra.FinitePresentation.of_finiteType.mp hft

/-- The original contraction and derived scalar origin of every specified nonempty
cell intersection have simultaneous affine arithmetic models, retaining both
endpoints and their original tensor-coordinate comparisons. -/
theorem exists_cell_contraction_models (a b : G.weylGroup)
    (S : Subalgebra ℤ K) (hS : S.FG) :
    ∃ R : Subalgebra ℤ K, S ≤ R ∧ R.FG ∧
      Nonempty (∀ w : {w : G.weylGroup // Nonempty (cellIntersection G a b w).left},
        FrobeniusSplitting.ArithmeticContractionModel (R := R)
          (cellContractionAlg G a b w.val) (cellOriginAlg G a b w.val w.property)) := by
  let : Finite G.weylGroup := ReductiveGroups.weylGroup_finite G.rootBase
  let I := {w : G.weylGroup // Nonempty (cellIntersection G a b w).left}
  let C (w : I) : Type u := cellCoefficients G a b w.val
  let (w : I) : Algebra.FinitePresentation K (C w) :=
    cellCoefficients_finitePres G a b w.val
  let vars (w : I) := Fin (Algebra.Presentation.ofFinitePresentationVars K (C w))
  let rels (w : I) := Fin (Algebra.Presentation.ofFinitePresentationRels K (C w))
  let P (w : I) : Algebra.Presentation K (C w) (vars w) (rels w) :=
    Algebra.Presentation.ofFinitePresentation K (C w)
  let σ (w : I) : C w →ₐ[K] Polynomial (C w) := cellContractionAlg G a b w.val
  let ε (w : I) : C w →ₐ[K] K := cellOriginAlg G a b w.val w.property
  have hOne : ∀ w : I, ∀ c : C w, (σ w c).eval 1 = c := by
    intro w c
    exact cellContractionAlg_one G a b w.val c
  have hZero : ∀ w : I, ∀ c : C w,
      (σ w c).eval 0 = algebraMap K (C w) (ε w c) := by
    intro w c
    exact cellContractionAlg_zero G a b w.val w.property c
  exact FrobeniusSplitting.exists_contraction_models (I := I) (K := K)
    C vars rels P σ ε hOne hZero S hS


end SchubertGeometry.CellContraction
