import OrbitComplexity.GroupActions.Varieties.ReductiveVariety
import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation

/-! # Conjugation automorphisms of reductive varieties

The coordinate Hopf-algebra inner automorphism induces the usual conjugation on group points.
-/

open CategoryTheory AlgebraicGeometry TauCeti

namespace GroupActions
noncomputable section
universe u
variable {K : Type u} [Field K] (G : ReductiveGroups.ReductiveGroupData K)

/-- Conjugation by a rational point is an automorphism of the reductive variety. -/
def reductiveConjugation (g : G.points) :
    (reductiveVariety G).toOver ≅ (reductiveVariety G).toOver :=
  (algSpec (CommRingCat.of K)).mapIso
    (CommAlgCat.isoMk (HopfAlgebra.pointConjugationBialgEquiv g).toAlgEquiv).op

/-- The algebraic conjugation automorphism induces ordinary conjugation of rational points. -/
theorem reductiveConjugation_points (g p : G.points) :
    Variety.mapPoints (reductiveConjugation G g).hom (reductivePointsEquiv G p) =
      reductivePointsEquiv G (g * p * g⁻¹) := by
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom p.ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (HopfAlgebra.pointConjugationBialgEquiv g).toAlgEquiv.toRingHom) =
    Spec.map (CommRingCat.ofHom (g * p * g⁻¹).ofConv.toRingHom)
  rw [← Spec.map_comp]
  have hp : WithConv.toConv (p.ofConv.comp (HopfAlgebra.pointConjugationAlgHom g)) =
      g * p * g⁻¹ := by
    simpa only [show Algebra.ofId K K = AlgHom.id K K from rfl,
      AlgHom.mapValue_id, MonoidHom.id_apply] using
      HopfAlgebra.comp_pointConjugationAlgHom g p
  exact congrArg (fun z : G.points => Spec.map (CommRingCat.ofHom z.ofConv.toRingHom)) hp

end
end GroupActions
