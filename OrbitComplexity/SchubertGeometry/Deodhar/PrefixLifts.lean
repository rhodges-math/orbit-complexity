import OrbitComplexity.SchubertGeometry.Deodhar.ParameterMaps

/-! # Regular group lifts of parameter prefixes

The ordered root product followed by its signed representative is a regular group-valued
map. Its projection is the flag morphism of the parameter prefix.
-/

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace SchubertGeometry
noncomputable section
open BruhatIntervals ReductiveGroups GroupActions GroupActions.Variety SchubertGeometry
universe u

private def constantMap {K : Type u} [Field K] (X H : Variety K) (h : H.points) :
    X.toOver ⟶ H.toOver := toUnit X.toOver ≫ H.pointsEquivOverHom h

private theorem constantMap_points {K : Type u} [Field K] (X H : Variety K)
    (h : H.points) (x : X.points) : mapPoints (constantMap X H h) x = h := by
  apply H.pointsEquivOverHom.injective
  change X.pointsEquivOverHom x ≫ (toUnit X.toOver ≫ H.pointsEquivOverHom h) = _
  rw [comp_toUnit_assoc]
  have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of K)))) = 𝟙 _ := toUnit_unique _ _
  rw [hu, Category.id_comp]

private theorem points_mul {K : Type u} [Field K] {X H : Variety K}
    [GrpObj H.toOver] (f g : X.toOver ⟶ H.toOver) (x : X.points) :
    mapPoints (f * g) x = mapPoints f x * mapPoints g x := by
  apply H.pointsEquivOverHom.injective
  rw [Variety.pointsEquivOverHom_mul]
  change X.pointsEquivOverHom x ≫ (f * g) =
    (X.pointsEquivOverHom x ≫ f) * (X.pointsEquivOverHom x ≫ g)
  exact MonObj.comp_mul _ _ _

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

private def affinePrefixLift (n : ℕ) :
    (affineSpaceVariety K (deodharIndex G expression)).toOver ⟶
      (reductiveVariety G).toOver :=
  subwordProductMorphism G expression n *
    constantMap (affineSpaceVariety K (deodharIndex G expression)) (reductiveVariety G)
      (reductivePointsEquiv G (subwordRepresentative G expression n))

/-- The root-product group lift of a parameter prefix is regular. -/
def deodharPrefixLift (n : ℕ) :
    (deodharParameters G expression).toOver ⟶ (reductiveVariety G).toOver :=
  deodharParameterInclusion G expression ≫ affinePrefixLift G expression n

/-- The regular group lift projects to the parameter-prefix flag morphism. -/
theorem deodharPrefixLift_projection (n : ℕ) :
    deodharPrefixLift G expression n ≫ flagQuotientMorphism G =
      deodharPrefixMorphism G expression n := by
  have h : affinePrefixLift G expression n ≫ flagQuotientMorphism G =
      subwordFlagMorphism G expression n := rfl
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => deodharParameterInclusion G expression ≫ f) h)

/-- Rational points of the group lift have the ordered product formula. -/
theorem deodharPrefixLift_points (n : ℕ) (x : (deodharParameters G expression).points) :
    mapPoints (deodharPrefixLift G expression n) x =
      reductivePointsEquiv G (subwordRootProduct G expression
        (fun j => affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
          (mapPoints (deodharParameterInclusion G expression) x) ⟨j⟩) n *
            subwordRepresentative G expression n) := by
  let y := mapPoints (deodharParameterInclusion G expression) x
  let c := constantMap (affineSpaceVariety K (deodharIndex G expression)) (reductiveVariety G)
    (reductivePointsEquiv G (subwordRepresentative G expression n))
  have hm := points_mul (subwordProductMorphism G expression n) c y
  have hp := subwordProductMorphism_points G expression n y
  have hc := constantMap_points (affineSpaceVariety K (deodharIndex G expression))
    (reductiveVariety G) (reductivePointsEquiv G (subwordRepresentative G expression n)) y
  have hmul := (reductivePointsMulEquiv G).map_mul
    (subwordRootProduct G expression
      (fun j => affineSpaceVarietyPointsEquiv K (deodharIndex G expression) y ⟨j⟩) n)
        (subwordRepresentative G expression n)
  exact (mapPoints_comp (deodharParameterInclusion G expression)
    (affinePrefixLift G expression n) x).trans
      (hm.trans ((congrArg₂ (fun a b => a * b) hp hc).trans hmul.symm))

end
end SchubertGeometry
