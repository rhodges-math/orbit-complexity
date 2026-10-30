import OrbitComplexity.GroupActions.Actions.Conjugation
import OrbitComplexity.GroupActions.Actions.InvariantSubvarieties
import OrbitComplexity.GroupActions.Actions.Restriction
import OrbitComplexity.GroupActions.Varieties.TorusPoints
import OrbitComplexity.GroupActions.Varieties.RootSubgroupPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.GroupRootTorus

/-! # Torus conjugation on root subgroups

The conjugation action of the reductive group restricts to its maximal torus and to every
closed positive-root subgroup. The closed inclusion is equivariant, and the rational-point
action is ambient group conjugation.

## Main definitions

* `GroupActions.torusConjugationAction`: torus conjugation on the reductive variety.
* `GroupActions.rootConjugationAction`: its restriction to a closed root subgroup.

## Main results

* `GroupActions.rootConjugationAction_isModHom`: equivariance of the closed inclusion.
* `GroupActions.rootConjugationAction_smul`: the ambient conjugation formula.
 -/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace GroupActions
variable {K : Type u} [Field K] [IsAlgClosed K]
  (G : ReductiveGroups.ReductiveGroupData K)

/-- The chosen torus acts on the reductive variety by conjugation. -/
@[instance_reducible]
def torusConjugationAction :
    ModObj (torusVariety G).toOver (reductiveVariety G).toOver := by
  letI := Variety.conjugationAction (reductiveVariety G)
  exact Mod.scalarRestriction (torusInclusion G) (reductiveVariety G).toOver

/-- The torus conjugation action conjugates ambient rational points. -/
theorem torusConjugationAction_smul (t : (torusVariety G).points) (g : G.points) :
    letI := torusConjugationAction G
    t • reductivePointsEquiv G g = reductivePointsEquiv G
      ((torusPointsMulEquiv G t : G.points) * g * (torusPointsMulEquiv G t : G.points)⁻¹) := by
  let := Variety.conjugationAction (reductiveVariety G)
  let := torusConjugationAction G
  rw [Variety.restricted_smul (torusInclusion G), torusInclusion_points]
  have h := Variety.conjugationAction_smul (reductiveVariety G)
    (reductivePointsEquiv G (torusPointsMulEquiv G t)) (reductivePointsEquiv G g)
  apply h.trans
  change reductivePointsMulEquiv G (torusPointsMulEquiv G t) *
      reductivePointsMulEquiv G g * (reductivePointsMulEquiv G (torusPointsMulEquiv G t))⁻¹ =
    reductivePointsMulEquiv G _
  rw [map_mul, map_mul, map_inv]

variable [CharZero K]

variable (R : Set G.rootIndex) (hR : ReductiveGroups.IsPositiveRootClosed G.rootBase R)

private theorem rootConjugation_stable :
    letI := torusConjugationAction G
    ∀ (t : (torusVariety G).points) (u : (rootSubsetVariety G R hR).points),
      t • Variety.mapPoints (rootSubsetInclusion G R hR) u ∈
        Set.range (Variety.mapPoints (rootSubsetInclusion G R hR)) := by
  let := torusConjugationAction G
  intro t u
  let c : G.rootSubsetPoints R hR :=
    ⟨(torusPointsMulEquiv G t : G.points) * (rootSubsetPointsMulEquiv G R hR u : G.points) *
        (torusPointsMulEquiv G t : G.points)⁻¹,
      G.rootSubsetPoints_conjugate_mem R hR _ _
        (torusPointsMulEquiv G t).property (rootSubsetPointsMulEquiv G R hR u).property⟩
  refine ⟨(rootSubsetPointsMulEquiv G R hR).symm c, ?_⟩
  rw [rootSubsetInclusion_points, MulEquiv.apply_symm_apply, rootSubsetInclusion_points,
    torusConjugationAction_smul]

/-- The torus acts algebraically by conjugation on a closed positive-root subgroup. -/
@[instance_reducible]
def rootConjugationAction :
    ModObj (torusVariety G).toOver (rootSubsetVariety G R hR).toOver := by
  letI := torusConjugationAction G
  exact Variety.modObjOfInvariant (torusVariety G) (reductiveVariety G)
    (rootSubsetVariety G R hR) (rootSubsetInclusion G R hR) (rootConjugation_stable G R hR)

/-- The root-subgroup inclusion is equivariant for torus conjugation. -/
theorem rootConjugationAction_isModHom :
    letI := torusConjugationAction G
    letI := rootConjugationAction G R hR
    IsModHom (torusVariety G).toOver (rootSubsetInclusion G R hR) := by
  let := torusConjugationAction G
  exact Variety.modObjOfInvariant_isModHom (torusVariety G) (reductiveVariety G)
    (rootSubsetVariety G R hR) (rootSubsetInclusion G R hR) (rootConjugation_stable G R hR)

/-- Conjugation on root-subgroup rational points agrees with ambient conjugation. -/
theorem rootConjugationAction_smul (t : (torusVariety G).points)
    (u : (rootSubsetVariety G R hR).points) :
    letI := rootConjugationAction G R hR
    (rootSubsetPointsMulEquiv G R hR (t • u) : G.points) =
      (torusPointsMulEquiv G t : G.points) * (rootSubsetPointsMulEquiv G R hR u : G.points) *
        (torusPointsMulEquiv G t : G.points)⁻¹ := by
  let := torusConjugationAction G
  let := rootConjugationAction G R hR
  apply (reductivePointsEquiv G).injective
  rw [← rootSubsetInclusion_points]
  have h := Variety.modObjOfInvariant_smul (torusVariety G) (reductiveVariety G)
    (rootSubsetVariety G R hR) (rootSubsetInclusion G R hR) (rootConjugation_stable G R hR) t u
  exact h.trans (by rw [rootSubsetInclusion_points, torusConjugationAction_smul])

end GroupActions
