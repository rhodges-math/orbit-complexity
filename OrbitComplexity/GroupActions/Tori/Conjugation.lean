import OrbitComplexity.GroupActions.Varieties.AffineAutomorphisms
import OrbitComplexity.GroupActions.Varieties.TorusPoints
import OrbitComplexity.ReductiveGroups.Groups.Reductive.TorusConjugation

/-! # Normalizer automorphisms of torus varieties

A rational point normalizing the maximal torus induces a group-variety automorphism of the
torus. On rational points it is conjugation by that normalizer point.

## Main definitions

* `GroupActions.torusConjugationIso`: the torus automorphism induced by a normalizer point.

## Main results

* `GroupActions.torusConjugationIso_points`: its rational-point conjugation formula.
-/

open CategoryTheory AlgebraicGeometry

namespace GroupActions

noncomputable section

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (G : ReductiveGroups.ReductiveGroupData K)

omit [IsAlgClosed K] in
private theorem torusConjReduced : IsReduced G.torusAlgebra := by
  have : Algebra.Smooth K G.torusAlgebra := G.torus_smooth
  exact TauCeti.isReduced_of_smooth K G.torusAlgebra

attribute [local instance] torusConjReduced

/-- A normalizer point induces an automorphism of the chosen torus variety. -/
def torusConjugationIso (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points)) :
    (torusVariety G).toOver ≅ (torusVariety G).toOver :=
  affineGroupIso (G.torusConjugation g hg)

/-- The normalizer automorphism of the torus variety preserves multiplication. -/
instance torusConjugationIso_isMonHom (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points)) :
    IsMonHom (torusConjugationIso G g hg).hom := by
  change IsMonHom (affineGroupIso (G.torusConjugation g hg)).hom
  infer_instance

omit [IsAlgClosed K] in
private theorem torusPointCoordinates (p : G.torusAlgebra →ₐ[K] K) :
    (torusPointsMulEquiv G ((affineVarietyPointsEquiv K G.torusAlgebra).symm p) : G.points) =
      WithConv.toConv (p.comp (Ideal.Quotient.mkₐ K G.torusIdeal.toIdeal)) := by
  apply (torusPointsMulEquiv_coe G (affinePointsEquiv p)).trans
  change WithConv.toConv ((affinePointsEquiv.symm (affinePointsEquiv p)).comp
    (Ideal.Quotient.mkₐ K G.torusIdeal.toIdeal)) = _
  rw [Equiv.symm_apply_apply]

/-- On torus rational points, the normalizer automorphism is ambient conjugation. -/
theorem torusConjugationIso_points (g : G.points)
    (hg : g ∈ Subgroup.normalizer (G.torusPoints : Set G.points))
    (t : (torusVariety G).points) :
    (torusPointsMulEquiv G (Variety.mapPoints (torusConjugationIso G g hg).hom t) :
      G.points) = g * (torusPointsMulEquiv G t : G.points) * g⁻¹ := by
  obtain ⟨p, rfl⟩ := (affinePointsEquiv : (G.torusAlgebra →ₐ[K] K) ≃
    (torusVariety G).points).surjective t
  change (torusPointsMulEquiv G
    (Variety.mapPoints (affineGroupIso (G.torusConjugation g hg)).hom
      ((affineVarietyPointsEquiv K G.torusAlgebra).symm p)) : G.points) = _
  have hp := affineGroupIso_points (G.torusConjugation g hg) p
  have h := congrArg (fun z : (affineVariety K G.torusAlgebra).points ↦
    (torusPointsMulEquiv G z : G.points)) hp
  apply h.trans
  exact (torusPointCoordinates G _).trans
    ((G.torusConjugation_points g hg (WithConv.toConv p)).trans
      (congrArg (fun t : G.points ↦ g * t * g⁻¹) (torusPointCoordinates G p).symm))

end

end GroupActions
