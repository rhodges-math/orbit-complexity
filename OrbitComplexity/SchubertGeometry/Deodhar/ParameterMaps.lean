import OrbitComplexity.SchubertGeometry.Deodhar.Parameters
import OrbitComplexity.SchubertGeometry.Deodhar.ProductMorphisms

/-! # Flag morphisms from Deodhar parameters

The open parameter coordinates restrict the ordered root-product morphisms. Each prefix has
the prescribed signed-representative point formula.

## Main definitions and results

* `deodharPrefixMorphism`: the flag morphism of a parameter prefix.
* `deodharPrefixMorphism_points`: its ordered-root point formula.
-/
open CategoryTheory
noncomputable section
namespace SchubertGeometry
open GroupActions GroupActions.Variety ReductiveGroups BruhatIntervals SchubertGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
  (G : ReductiveGroupData K) {word : List G.rootBase.support}
  (expression : Subexpression word)

/-- The parameter variety maps to flags by the root product of its first `n` positions. -/
def deodharPrefixMorphism (n : ℕ) :
    (deodharParameters G expression).toOver ⟶ (flagVariety G).toOver :=
  deodharParameterInclusion G expression ≫ subwordFlagMorphism G expression n

/-- The parameter morphism has the ordered root-product and signed-representative formula. -/
theorem deodharPrefixMorphism_points (n : ℕ)
    (x : (deodharParameters G expression).points) :
    mapPoints (deodharPrefixMorphism G expression n) x =
      flagVarietyPointsEquiv G (flagProjection G
        (subwordRootProduct G expression
          (fun j => affineSpaceVarietyPointsEquiv K (deodharIndex G expression)
            (mapPoints (deodharParameterInclusion G expression) x) ⟨j⟩) n *
              subwordRepresentative G expression n)) := by
  exact (mapPoints_comp (deodharParameterInclusion G expression)
    (subwordFlagMorphism G expression n) x).trans
      (subwordFlagMorphism_points G expression n
        (mapPoints (deodharParameterInclusion G expression) x))

end SchubertGeometry
