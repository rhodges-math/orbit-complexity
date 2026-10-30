import OrbitComplexity.ReductiveGroups.Groups.Representations.AffineGroupConjugationMorphism
import OrbitComplexity.ReductiveGroups.Groups.Additive.GaAffineGroupPoints

/-!
# Conjugation of additive one-parameter subgroups

Precomposition with the coordinate conjugation map conjugates every rational
point of an additive one-parameter subgroup.
-/

noncomputable section

namespace ReductiveGroups

open TauCeti

variable {K B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

/-- Precomposing a one-parameter coordinate map with conjugation conjugates its points. -/
theorem gaPoints_comp_conjugation (x : B →ₐc[K] SymmetricAlgebra K K)
    (g : WithConv (B →ₐ[K] K)) (t : Multiplicative K) :
    gaAffineGroupPoints (x.comp (affineGroupConjugationBialgHom g)) t =
      g * gaAffineGroupPoints x t * g⁻¹ := by
  change WithConv.toConv
      ((gaAffineGroupPoints x t).ofConv.comp (affineGroupConjugationAlgHom g)) = _
  simpa only [show IsScalarTower.toAlgHom K K K = AlgHom.id K K from rfl,
    AlgHom.id_comp, WithConv.toConv_ofConv] using
    affineGroupConjugationAlgHom_point g (gaAffineGroupPoints x t)

end ReductiveGroups
