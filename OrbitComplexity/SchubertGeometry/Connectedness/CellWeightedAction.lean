import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CellIntersection
import OrbitComplexity.SchubertGeometry.Connectedness.CellEquivariance
import OrbitComplexity.SchubertGeometry.Connectedness.PositiveCocharacter
import OrbitComplexity.FrobeniusSplitting.Normality.WeightedLaurent
import OrbitComplexity.GroupActions.Varieties.AffineTensorAction
import OrbitComplexity.GroupActions.Actions.ActionMapSquares
import OrbitComplexity.GroupActions.Tori.RootWeights

/-!
# Positive cocharacter action in the original cell coordinates

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

noncomputable section

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

@[instance_reducible]
private def cellCoordinateAction (w : G.weylGroup) :
    ModObj (GroupActions.torusVariety G).toOver
      ((Spec (.of (cellAlgebra G w))).asOver (Spec (.of K))) :=
  GroupActions.weightedAffineAction G (fun r :
    {r : G.rootIndex // G.rootBase.IsPos r ∧
      r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w} =>
        (G.rootCharacter r.val).toAdd)

private def cellCoordinateSmul (w : G.weylGroup) :
    (GroupActions.torusVariety G).toOver ⊗
      ((Spec (.of (cellAlgebra G w))).asOver (Spec (.of K))) ⟶
        (Spec (.of (cellAlgebra G w))).asOver (Spec (.of K)) := by
  letI := cellCoordinateAction G w
  exact γ[(GroupActions.torusVariety G).toOver,
    ((Spec (.of (cellAlgebra G w))).asOver (Spec (.of K)))]

/-- The positive integral weight of each original inversion-root coordinate. -/
def cellWeight (w : G.weylGroup)
    (r : {r : G.rootIndex // G.rootBase.IsPos r ∧
      r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w}) : ℕ :=
  (2 * G.rootBase.height r.val).toNat

/-- Every coordinate weight is strictly positive. -/
theorem cellWeight_pos (w : G.weylGroup)
    (r : {r : G.rootIndex // G.rootBase.IsPos r ∧
      r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w}) :
    0 < cellWeight G w r := by
  have hp : 0 < G.rootBase.height r.val := r.property.1
  dsimp only [cellWeight]
  omega

/-- The original ambient cell contraction, before imposing the closed ideal. -/
def cellWeightedMap (w : G.weylGroup) :
    cellAlgebra G w →ₐ[K] Polynomial (cellAlgebra G w) :=
  FrobeniusSplitting.weightedCoordinateMap (cellWeight G w)

/-- Extend the specified cocharacter parameter to arbitrary coefficient algebras. -/
def cellParameterMap (C : Type u) [CommRing C] [Algebra K C] :
    G.torusAlgebra →ₐ[K] LaurentPolynomial C :=
  (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId K C)).comp (positiveTorusAlgebra G)

private def cellParameterOver (C : Type u) [CommRing C] [Algebra K C] :
    (Spec (.of (LaurentPolynomial C))).asOver (Spec (.of K)) ⟶
      (GroupActions.torusVariety G).toOver :=
  GroupActions.algebraSpecMap (cellParameterMap G C)

/-- The cocharacter has exactly the original positive coordinate weight. -/
theorem cellParameterMap_root (C : Type u) [CommRing C] [Algebra K C]
    (w : G.weylGroup)
    (r : {r : G.rootIndex // G.rootBase.IsPos r ∧
      r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w}) :
    cellParameterMap G C ((GroupActions.torusCoordinateEquiv G).symm
      (MonoidAlgebra.single (G.rootCharacter r.val) 1)) =
        LaurentPolynomial.T (cellWeight G w r : ℤ) := by
  rw [cellParameterMap, AlgHom.comp_apply, positiveTorusAlgebra_root]
  have hn : (cellWeight G w r : ℤ) = 2 * G.rootBase.height r.val := by
    dsimp only [cellWeight]
    exact Int.toNat_of_nonneg (by have hp : 0 < G.rootBase.height r.val := r.property.1; omega)
  rw [hn]
  change AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId K C)
    (AddMonoidAlgebra.single (2 * G.rootBase.height r.val) 1) = _
  rw [AddMonoidAlgebra.mapAlgHom_single, map_one]
  rfl

omit [CharZero K] in
/-- The already defined diagonal action has the specified coordinate map. -/
theorem weightedAffine_coordinates {J : Type u} [Finite J]
    (χ : J → G.torusIndex →₀ ℤ) :
    let := GroupActions.weightedAffineAction G χ
    (γ[(GroupActions.torusVariety G).toOver,
      (GroupActions.affineSpaceVariety K J).toOver]).left =
      (pullbackSpecIso K G.torusAlgebra (MvPolynomial J K)).hom ≫
        Spec.map (CommRingCat.ofHom
          (FrobeniusSplitting.diagonalCoordinates (fun i =>
            (GroupActions.torusCoordinateEquiv G).symm
              (MonoidAlgebra.single (Multiplicative.ofAdd (χ i)) 1))).toRingHom) := rfl

/-- The original cell chart is equivariant as a morphism of the specified torus actions. -/
theorem cellChartOver_equivariant (w : G.weylGroup) :
    let := cellCoordinateAction G w
    IsModHom (GroupActions.torusVariety G).toOver (cellChartOver G w).hom := by
  let := GroupActions.weightedAffineAction G (fun r :
    {r : G.rootIndex // G.rootBase.IsPos r ∧
      r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w} =>
        (G.rootCharacter r.val).toAdd)
  let := cellCoordinateAction G w
  let := GroupActions.rootConjugationAction G
    (ReductiveGroups.leftRootInversionIndices G.rootBase w)
    (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
  let := GroupActions.rootSubsetChart_isModHom G
    (ReductiveGroups.leftRootInversionIndices G.rootBase w)
    (ReductiveGroups.LeftRootInversionIndices.isPositiveRootClosed G.rootBase w)
  let := schubertCellIso_equivariant G w
  exact inferInstanceAs (IsModHom (GroupActions.torusVariety G).toOver
    ((schubertUnipotentChart G w).hom ≫ (schubertCellIso G w).hom))

private def cellPointOver {C : Type u} [CommRing C] [Algebra K C]
    (w : G.weylGroup) (q : cellAlgebra G w →ₐ[K] C) :
    (Spec (.of (LaurentPolynomial C))).asOver (Spec (.of K)) ⟶
      (schubertCell G w).toOver :=
  GroupActions.algebraSpecMap (FrobeniusSplitting.laurentConstants q) ≫
    (cellChartOver G w).hom

/-- The punctured polynomial family is the specified positive-cocharacter action,
for any algebra-valued coordinate point of the original cell chart. -/
theorem cellWeightedMap_action {C : Type u} [CommRing C] [Algebra K C]
    (w : G.weylGroup) (q : cellAlgebra G w →ₐ[K] C) :
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent.comp
      ((Polynomial.mapRingHom q.toRingHom).comp (cellWeightedMap G w).toRingHom))) ≫
        (cellCoordinateIso G w).hom =
      ((cellParameterOver G C) •
        (cellPointOver G w q)).left := by
  let χ := fun r : {r : G.rootIndex // G.rootBase.IsPos r ∧
      r ∈ ReductiveGroups.leftRootInversionIndices G.rootBase w} =>
        (G.rootCharacter r.val).toAdd
  have hring := FrobeniusSplitting.weightedLaurent_diagonal (cellWeight G w)
    (fun r => (GroupActions.torusCoordinateEquiv G).symm
      (MonoidAlgebra.single (G.rootCharacter r.val) 1)) q
    (cellParameterMap G C) (cellParameterMap_root G C w)
  have hspec := GroupActions.affineTensor_action (R := K) (H := G.torusAlgebra)
    (A := cellAlgebra G w) (D := LaurentPolynomial C)
    (cellCoordinateSmul G w)
    (FrobeniusSplitting.diagonalCoordinates (fun r =>
      (GroupActions.torusCoordinateEquiv G).symm
        (MonoidAlgebra.single (G.rootCharacter r.val) 1)))
    (weightedAffine_coordinates G χ) (cellParameterMap G C)
    (FrobeniusSplitting.laurentConstants q)
  have hc : Spec.map (CommRingCat.ofHom (Polynomial.toLaurent.comp
      ((Polynomial.mapRingHom q.toRingHom).comp (cellWeightedMap G w).toRingHom))) =
      (lift (cellParameterOver G C)
        (GroupActions.algebraSpecMap (FrobeniusSplitting.laurentConstants q)) ≫
          cellCoordinateSmul G w).left := by
    exact (congrArg (fun f : cellAlgebra G w →+* LaurentPolynomial C =>
      Spec.map (CommRingCat.ofHom f)) hring).trans hspec.symm
  rw [hc]
  have ha := GroupActions.actionMap_chart (cellCoordinateAction G w)
    (inferInstance : ModObj (GroupActions.torusVariety G).toOver
      (schubertCell G w).toOver)
    (cellChartOver G w).hom (cellChartOver_equivariant G w)
    (cellParameterOver G C)
    (GroupActions.algebraSpecMap (FrobeniusSplitting.laurentConstants q))
  exact congrArg Over.Hom.left ha

end SchubertGeometry.CellContraction
