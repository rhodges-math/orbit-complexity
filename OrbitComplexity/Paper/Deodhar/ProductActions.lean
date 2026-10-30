import OrbitComplexity.Paper.Deodhar.ProductMorphisms
import OrbitComplexity.GroupActions.Tori.WeightedAction
import OrbitComplexity.GroupActions.Actions.EquivariantPoints
import OrbitComplexity.SchubertGeometry.Cells.Stability
import OrbitComplexity.SchubertGeometry.Deodhar.ProductMorphisms
import OrbitComplexity.Paper.Deodhar.Products

/-! # Torus equivariance of root-product flag morphisms

The negative signed-root characters give a diagonal torus action on the selected affine
coordinates. The root-product flag morphism is equivariant for that algebraic action.

## Main results

* `subwordFlagMorphism_isModHom`: equivariance of every prefix flag morphism.

## References

* Y. Gao and R. Hodges, *Orbit structures and complexity in Schubert and Richardson varieties*,
  Theorem 1.4.
-/
open CategoryTheory AlgebraicGeometry

noncomputable section
namespace SchubertOrbits
open GroupActions GroupActions.Variety ReductiveGroups BruhatIntervals SchubertGeometry
open SchubertOrbits
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

local notation "Positions" => {position : Fin word.length //
  position ∈ equalSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression ∪
    negativeSteps (ReductiveGroups.weylCoxeterSystem G.rootBase) expression}

omit [IsAlgClosed K] [CharZero K] in
private theorem torusReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra
attribute [local instance] torusReduced

private theorem flagMorphism_smul (n : ℕ) (t : (torusVariety G).points)
    (x : (affineSpaceVariety K (ULift.{u} Positions)).points) :
    letI := weightedAffineAction G (fun j : ULift.{u} Positions =>
      (subwordCharacter G expression j.down).toAdd)
    mapPoints (SchubertGeometry.subwordFlagMorphism G expression n) (t • x) =
      t • mapPoints (SchubertGeometry.subwordFlagMorphism G expression n) x := by
  let := weightedAffineAction G (fun j : ULift.{u} Positions =>
    (subwordCharacter G expression j.down).toAdd)
  let parameters := fun j : Positions =>
    affineSpaceVarietyPointsEquiv K (ULift.{u} Positions) x ⟨j⟩
  let scaled := fun j : Positions => affinePointsEquiv.symm t
    ((torusCoordinateEquiv G).symm (MonoidAlgebra.single (subwordCharacter G expression j) 1)) *
      parameters j
  have hcoords : (fun j : Positions =>
      affineSpaceVarietyPointsEquiv K (ULift.{u} Positions) (t • x) ⟨j⟩) = scaled := by
    funext j
    exact (weightedAffineAction_smul G (fun k : ULift.{u} Positions =>
      (subwordCharacter G expression k.down).toAdd) t x (ULift.up j)).trans (mul_comm _ _)
  calc
    _ = flagVarietyPointsEquiv G (flagProjection G
        (SchubertGeometry.subwordRootProduct G expression
          (fun j => affineSpaceVarietyPointsEquiv K (ULift.{u} Positions) (t • x) ⟨j⟩) n *
            SchubertGeometry.subwordRepresentative G expression n)) :=
      SchubertGeometry.subwordFlagMorphism_points G expression n (t • x)
    _ = flagVarietyPointsEquiv G (flagProjection G
        (SchubertGeometry.subwordRootProduct G expression scaled n *
          SchubertGeometry.subwordRepresentative G expression n)) :=
      congrArg (fun p => flagVarietyPointsEquiv G (flagProjection G
        (SchubertGeometry.subwordRootProduct G expression p n *
          SchubertGeometry.subwordRepresentative G expression n))) hcoords
    _ = flagVarietyPointsEquiv G ((torusPointsMulEquiv G t : G.points) • flagProjection G
        (SchubertGeometry.subwordRootProduct G expression parameters n *
          SchubertGeometry.subwordRepresentative G expression n)) :=
      congrArg (flagVarietyPointsEquiv G)
        (subwordRootProduct_flag_action G expression parameters n t).symm
    _ = t • flagVarietyPointsEquiv G (flagProjection G
        (SchubertGeometry.subwordRootProduct G expression parameters n *
          SchubertGeometry.subwordRepresentative G expression n)) :=
      (torusFlag_smul G t _).symm
    _ = _ := congrArg (fun y => t • y) (SchubertGeometry.subwordFlagMorphism_points G
      expression n x).symm

/-- The selected-root flag morphism is equivariant for its diagonal torus character action. -/
theorem subwordFlagMorphism_isModHom (n : ℕ) :
    letI := weightedAffineAction G (fun j : ULift.{u} Positions =>
      (subwordCharacter G expression j.down).toAdd)
    IsModHom (torusVariety G).toOver (SchubertGeometry.subwordFlagMorphism G expression n) := by
  let := weightedAffineAction G (fun j : ULift.{u} Positions =>
    (subwordCharacter G expression j.down).toAdd)
  exact isModHom_of_points (torusVariety G)
    (affineSpaceVariety K (ULift.{u} Positions)) (flagVariety G)
    (SchubertGeometry.subwordFlagMorphism G expression n) (flagMorphism_smul G expression n)

end SchubertOrbits
