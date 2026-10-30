import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupConjugationMorphism
import OrbitComplexity.ReductiveGroups.Groups.Tangents.ClosedSubgroupIntersectionTangent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation

/-!
# Tangents of conjugate closed subgroups

The adjoint action carries the tangent image of a closed subgroup onto the
tangent image of its conjugate. The coordinate conjugation morphism computes
the adjoint differential directly.

## Main definitions

* `ReductiveGroups.hopfTangentImage`: the tangent image of a Hopf quotient.

## Main results

* `ReductiveGroups.conjugate_tangentImage`: the tangent image after conjugation.
-/

noncomputable section

namespace ReductiveGroups

open TauCeti

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- The image of the tangent Lie algebra of a closed subgroup in the ambient tangent algebra. -/
abbrev hopfTangentImage (I : HopfIdeal K B) :
    LieSubalgebra K (Derivation K B (Bialgebra.CounitAlgebra K B K)) :=
  (derivationCompLieHom (B := K)
    (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of K B) I).hom).range

/-- The specialized coordinate conjugation morphism is the point-conjugation algebra map. -/
theorem conjugationAlgHom_eq_point (g : WithConv (B →ₐ[K] K)) :
    affineGroupConjugationAlgHom g = HopfAlgebra.pointConjugationAlgHom g := by
  rfl

/-- The adjoint action maps a subgroup tangent vector into the conjugate subgroup tangent. -/
theorem adjoint_mem_conjugate_tangent (I : HopfIdeal K B) (g : WithConv (B →ₐ[K] K))
    (d : Derivation K B (Bialgebra.CounitAlgebra K B K)) (hd : d ∈ hopfTangentImage I) :
    affineGroupAdjointLieEquiv g d ∈ hopfTangentImage (I.conjugate g) := by
  apply (tangent_mem_hopfQuotient_iff (I.conjugate g) _).mpr
  intro a ha
  have hder : affineGroupAdjointLieEquiv g d =
      derivationComp (B := K) (affineGroupConjugationBialgHom g) d := by
    simpa only [affineGroupAdjointLieEquiv_apply, affineGroupAdjointRepresentation_apply] using
      (DerivationComp.conjugation g d).symm
  rw [hder]
  change d (affineGroupConjugationAlgHom g a) = 0
  rw [conjugationAlgHom_eq_point]
  exact (tangent_mem_hopfQuotient_iff I d).mp hd _ (HopfIdeal.mem_conjugate.mp ha)

/-- Conjugation carries the subgroup tangent image exactly onto its adjoint transform. -/
theorem conjugate_tangentImage (I : HopfIdeal K B) (g : WithConv (B →ₐ[K] K)) :
    (hopfTangentImage (I.conjugate g)).toSubmodule =
      (hopfTangentImage I).toSubmodule.map
        ((affineGroupAdjointLieEquiv g).toLinearEquiv :
          Derivation K B (Bialgebra.CounitAlgebra K B K) →ₗ[K] _) := by
  ext d
  constructor
  · intro hd
    let x := affineGroupAdjointLieEquiv g⁻¹ d
    have hx : x ∈ hopfTangentImage I := by
      have h := adjoint_mem_conjugate_tangent (I.conjugate g) g⁻¹ d hd
      simpa only [x, HopfIdeal.conjugate_inv_conjugate] using h
    have hxeq : affineGroupAdjointLieEquiv g x = d := by
      change affineGroupAdjointRepresentation g (affineGroupAdjointRepresentation g⁻¹ d) = d
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    exact Submodule.mem_map.mpr ⟨x, hx, hxeq⟩
  · intro hd
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hd
    exact adjoint_mem_conjugate_tangent I g x hx

end ReductiveGroups
