import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Batteries.Tactic.Lint
import OrbitComplexity.SchubertGeometry.Connectedness.CellIntersection
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootCoordinatePoints
import OrbitComplexity.GroupActions.Varieties.AffineMorphisms

/-!
# The origin of the original root-cell chart

-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SchubertGeometry.CellContraction

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

universe u

private theorem overIso_trans_hom {S : Scheme.{u}} {X Y Z : Over S}
    (e : X ≅ Y) (f : Y ≅ Z) :
    ((Over.forget S).mapIso (e ≪≫ f)).hom = e.hom.left ≫ f.hom.left := rfl

private theorem overPoint_chart {S D : Scheme.{u}} {A B X Y : Over S}
    (e : A ≅ B) (f : B ≅ X) (i : X ⟶ Y) (p : D ⟶ A.left) (z : D ⟶ Y.left)
    (h : p ≫ (e.hom ≫ f.hom ≫ i).left = z) :
    p ≫ ((Over.forget S).mapIso (e ≪≫ f)).hom ≫ i.left = z := by
  rw [overIso_trans_hom]
  simpa only [Over.comp_left, Category.assoc] using h

private theorem pointOver_left {K : Type u} [Field K]
    (X : GroupActions.Variety K) (x : X.points) :
    (X.pointsEquivOverHom x).left = x.val := rfl

private theorem affineSpacePoint_value {K J : Type u} [Field K] [Finite J]
    (a : J → K) :
    ((GroupActions.affineSpaceVarietyPointsEquiv K J).symm a).val =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval a).toRingHom) := by
  rfl

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (G : ReductiveGroups.ReductiveGroupData K)

private theorem prod_map_one {H ι : Type*} [Monoid H] (l : List ι) :
    (l.map (fun _ => (1 : H))).prod = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simpa only [List.map_cons, List.prod_cons, one_mul] using ih

/-- The ordered root chart evaluates to the original ordered root product. -/
theorem rootChart_points (R : Set G.rootIndex)
    (hR : ReductiveGroups.IsPositiveRootClosed G.rootBase R)
    (a : {r : G.rootIndex // G.rootBase.IsPos r ∧ r ∈ R} → K) :
    (GroupActions.rootSubsetPointsMulEquiv G R hR
      (GroupActions.Variety.mapPoints (GroupActions.rootSubsetChart G R hR).hom
        ((GroupActions.affineSpaceVarietyPointsEquiv K _).symm a)) : G.points) =
      ((G.rootSubsetOrder R).map (fun i =>
        ReductiveGroups.gaParameterPoint (G.borelRootMaps i.val)
          (a (G.rootSubsetIndexEquiv R i)))).prod := by
  let e : (GroupActions.affineVariety K (G.rootSubsetAlgebra R hR)).points ≃*
      G.rootSubsetPoints R hR := GroupActions.rootSubsetPointsMulEquiv G R hR
  change (e
    (GroupActions.Variety.mapPoints
      (GroupActions.affineMorphism (G.rootSubsetCoordinateEquiv R hR).toAlgHom)
      ((GroupActions.affineVarietyPointsEquiv K _).symm (MvPolynomial.aeval a))) :
        G.points) = _
  rw [GroupActions.affineMorphism_points]
  have h := G.rootSubsetCoordinateEquiv_eval R hR a
  apply WithConv.ofConv_injective
  change ((GroupActions.affinePointsEquiv.symm (GroupActions.affinePointsEquiv
    ((MvPolynomial.aeval a).comp (G.rootSubsetCoordinateEquiv R hR).toAlgHom))).comp
      (Ideal.Quotient.mkₐ K (G.rootSubsetIdeal R hR).toIdeal)) = _
  rw [Equiv.symm_apply_apply]
  exact h

/-- Zero root parameters represent the identity in the original root subgroup. -/
theorem rootChart_zero_points (R : Set G.rootIndex)
    (hR : ReductiveGroups.IsPositiveRootClosed G.rootBase R) :
    (GroupActions.rootSubsetPointsMulEquiv G R hR
      (GroupActions.Variety.mapPoints (GroupActions.rootSubsetChart G R hR).hom
        ((GroupActions.affineSpaceVarietyPointsEquiv K _).symm (fun _ => 0))) :
          G.points) = 1 := by
  rw [rootChart_points]
  simp only [ReductiveGroups.gaParameterPoint_zero]
  exact prod_map_one _

/-- The origin of the original cell chart is its specified Weyl rational flag. -/
theorem cellChart_origin_points (w : G.weylGroup) :
    GroupActions.Variety.mapPoints
      ((schubertUnipotentChart G w).hom ≫ (schubertCellIso G w).hom ≫
        schubertCellInclusion G w)
      ((GroupActions.affineSpaceVarietyPointsEquiv K _).symm (fun _ => 0)) =
        weylFlagPoint G w := by
  simp only [schubertCellIso_hom_comp,
    GroupActions.Variety.mapPoints_comp, schubertRootMorphism_points]
  rw [rootChart_zero_points, one_mul]
  rfl

/-- The zero-coordinate spectrum section has exactly the chosen Weyl flag image. -/
theorem cellChart_origin (w : G.weylGroup) :
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (fun _ => (0 : K)) : cellAlgebra G w →ₐ[K] K).toRingHom) ≫
        (cellCoordinateIso G w).hom ≫ (schubertCellInclusion G w).left =
      ((flagVariety G).pointsEquivOverHom (weylFlagPoint G w)).left := by
  have h := congrArg Subtype.val (cellChart_origin_points G w)
  simp only [GroupActions.Variety.mapPoints] at h
  rw [affineSpacePoint_value] at h
  have hp := overPoint_chart (schubertUnipotentChart G w) (schubertCellIso G w)
    (schubertCellInclusion G w)
    (Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (fun _ => (0 : K)) : cellAlgebra G w →ₐ[K] K).toRingHom))
    (weylFlagPoint G w).val h
  exact hp.trans (pointOver_left (flagVariety G) (weylFlagPoint G w)).symm

end SchubertGeometry.CellContraction
