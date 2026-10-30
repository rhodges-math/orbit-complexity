import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CellCoefficients
import OrbitComplexity.SchubertGeometry.Connectedness.CellWeightedAction

/-!
# The original closed-intersection ideal vanishes on the Laurent family

Use the universal Laurent coordinate point of the original intersection and
its specified torus action. Both pullback projections are retained. This gives a
scheme-map factorization through the same intersection, hence a specified ring
factorization and the Laurent kernel identity, including nilpotents.

-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u

attribute [local instance] coefficientAlgebra

section Generic

variable {C : Type u} [Category C] {A X I D : C}

/-- Cancel an arbitrary chart isomorphism once, before substituting a cell chart. -/
theorem factor_of_chart_square (e : A ≅ X) (i : I ⟶ X)
    (l : D ⟶ A) (f : D ⟶ I) (h : l ≫ e.hom = f ≫ i) :
    l = f ≫ i ≫ e.inv := by
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Transport a factorization through the specified coordinate counit. -/
theorem factor_through_counit (e : A ≅ I) (i : I ⟶ X)
    (q : A ⟶ X) (hq : q = e.hom ≫ i)
    (l : D ⟶ X) (f : D ⟶ I) (hl : l = f ≫ i) :
    l = (f ≫ e.inv) ≫ q := by
  rw [hq]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hl

end Generic

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

private theorem weightedMap_action_at {C : Type u} [CommRing C] [Algebra K C]
    (w : G.weylGroup) (q : cellAlgebra G w →ₐ[K] C)
    (t : (Spec (.of (LaurentPolynomial C))).asOver (Spec (.of K)) ⟶
      (GroupActions.torusVariety G).toOver)
    (p : (Spec (.of (LaurentPolynomial C))).asOver (Spec (.of K)) ⟶
      (schubertCell G w).toOver)
    (ht : t = GroupActions.algebraSpecMap (cellParameterMap G C))
    (hp : p = GroupActions.algebraSpecMap (FrobeniusSplitting.laurentConstants q) ≫
      (cellChartOver G w).hom) :
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent.comp
      ((Polynomial.mapRingHom q.toRingHom).comp (cellWeightedMap G w).toRingHom))) ≫
        (cellCoordinateIso G w).hom = (t • p).left := by
  subst t p
  exact cellWeightedMap_action G w q

/-- The Laurent spectrum of the specified coefficient ring, over the original field. -/
abbrev cellLaurentSource (a b w : G.weylGroup) :=
  (Spec (.of (LaurentPolynomial (cellCoefficients G a b w)))).asOver (Spec (.of K))

/-- The original intersection point with constant coordinates on the Laurent parameter. -/
def cellLaurentPoint (a b w : G.weylGroup) :
    cellLaurentSource G a b w ⟶ cellIntersection G a b w :=
  GroupActions.algebraSpecMap
    (IsScalarTower.toAlgHom K (cellCoefficients G a b w)
      (LaurentPolynomial (cellCoefficients G a b w))) ≫
    (coefficientIso (cellIntersection G a b w)).hom

/-- The specified cocharacter parameter over the same universal Laurent point. -/
def cellLaurentTorus (a b w : G.weylGroup) :
    cellLaurentSource G a b w ⟶ (GroupActions.torusVariety G).toOver :=
  GroupActions.algebraSpecMap (cellParameterMap G (cellCoefficients G a b w))

/-- The given Laurent action on the original intersection. -/
def cellLaurentFamily (a b w : G.weylGroup) :
    cellLaurentSource G a b w ⟶ cellIntersection G a b w :=
  lift (cellLaurentTorus G a b w) (cellLaurentPoint G a b w) ≫ cellTorusFamily G a b w

/-- The universal Laurent family has its original cell projection. -/
theorem cellLaurentFamily_fst (a b w : G.weylGroup) :
    cellLaurentFamily G a b w ≫
        pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b) =
      cellLaurentTorus G a b w • (cellLaurentPoint G a b w ≫
        pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)) := by
  rw [cellLaurentFamily, Category.assoc, cellTorusFamily_fst, ModObj.comp_smul]
  simp only [lift_fst, lift_snd_assoc]

/-- The same universal family also has its original Richardson projection. -/
theorem cellLaurentFamily_snd (a b w : G.weylGroup) :
    cellLaurentFamily G a b w ≫
        pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b) =
      cellLaurentTorus G a b w • (cellLaurentPoint G a b w ≫
        pullback.snd (schubertCellInclusion G w) (richardsonInclusion G a b)) := by
  rw [cellLaurentFamily, Category.assoc, cellTorusFamily_snd, ModObj.comp_smul]
  simp only [lift_fst, lift_snd_assoc]

/-- Extending the original coordinate map gives precisely the original Laurent cell point. -/
theorem cellLaurentPoint_chart (a b w : G.weylGroup) :
    GroupActions.algebraSpecMap
        (FrobeniusSplitting.laurentConstants (cellIntersectionAlgMap G a b w)) ≫
          (cellChartOver G w).hom =
      cellLaurentPoint G a b w ≫
        pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b) := by
  rw [FrobeniusSplitting.laurentConstants, GroupActions.algebraSpecMap_comp,
    Category.assoc, cellIntersectionAlgMap_over, cellLaurentPoint, Category.assoc]

/-- The Laurent coordinate substitution of the original ambient weighted family. -/
def cellLaurentPullback (a b w : G.weylGroup) :
    cellAlgebra G w →+* LaurentPolynomial (cellCoefficients G a b w) :=
  Polynomial.toLaurent.comp
    ((Polynomial.mapRingHom (cellIntersectionAlgMap G a b w).toRingHom).comp
      (cellWeightedMap G w).toRingHom)

/-- The original Laurent substitution is the given family on the same intersection. -/
theorem cellLaurentFamily_square (a b w : G.weylGroup) :
    Spec.map (CommRingCat.ofHom (cellLaurentPullback G a b w)) ≫
        (cellCoordinateIso G w).hom =
      (cellLaurentFamily G a b w).left ≫
        (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left := by
  have h := weightedMap_action_at G w (cellIntersectionAlgMap G a b w)
    (cellLaurentTorus G a b w)
    (cellLaurentPoint G a b w ≫
      pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b))
    rfl (cellLaurentPoint_chart G a b w).symm
  exact h.trans (congrArg Over.Hom.left (cellLaurentFamily_fst G a b w)).symm

/-- Every element of the original closed-intersection ideal vanishes under the
same Laurent family, without any reducedness assumption on the intersection. -/
theorem cellIntersectionLaurent_ideal (a b w : G.weylGroup)
    (f : cellAlgebra G w) (hf : cellIntersectionAlgMap G a b w f = 0) :
    Polynomial.toLaurent
      (Polynomial.map (cellIntersectionAlgMap G a b w).toRingHom
        (cellWeightedMap G w f)) = 0 := by
  have hl := factor_of_chart_square (cellCoordinateIso G w)
    (pullback.fst (schubertCellInclusion G w) (richardsonInclusion G a b)).left
    (Spec.map (CommRingCat.ofHom (cellLaurentPullback G a b w)))
    (cellLaurentFamily G a b w).left (cellLaurentFamily_square G a b w)
  have hq : Spec.map (CommRingCat.ofHom
      (cellIntersectionAlgMap G a b w).toRingHom) =
        (coefficientIso (cellIntersection G a b w)).hom.left ≫
          (cellChartMapOver G a b w).left :=
    chartAlgHom_square (cellIntersection G a b w) (cellChartMapOver G a b w)
  have hs := factor_through_counit
    ((Over.forget (Spec (.of K))).mapIso (coefficientIso (cellIntersection G a b w)))
    (cellChartMapOver G a b w).left
    (Spec.map (CommRingCat.ofHom (cellIntersectionAlgMap G a b w).toRingHom)) hq
    (Spec.map (CommRingCat.ofHom (cellLaurentPullback G a b w)))
    (cellLaurentFamily G a b w).left hl
  exact zero_of_spec_factor (cellIntersectionAlgMap G a b w).toRingHom
    (cellLaurentPullback G a b w)
    ((cellLaurentFamily G a b w).left ≫
      (coefficientIso (cellIntersection G a b w)).inv.left) hs f hf

end SchubertGeometry.CellContraction
