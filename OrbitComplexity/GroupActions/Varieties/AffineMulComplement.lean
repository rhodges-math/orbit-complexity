import OrbitComplexity.GroupActions.Varieties.AffineMulTangents

/-!
# Complementary tangent images

The tangent of a closed subgroup identifies with its image in the ambient tangent algebra.
For complementary images, addition is a linear equivalence and the restricted multiplication
differential is bijective.

## Main results

* `GroupActions.affineMulTangent_bijective_of_isCompl`: the complementary-image criterion.
-/

namespace GroupActions

noncomputable section

open scoped TensorProduct

universe u

variable {R H A B : Type u} [CommRing R]
  [CommRing H] [Bialgebra R H]
  [CommRing A] [Bialgebra R A]
  [CommRing B] [Bialgebra R B]

/-- Complementary subgroup tangent images make the multiplication differential bijective. -/
theorem affineMulTangent_bijective_of_isCompl (f : H →ₐc[R] A) (g : H →ₐc[R] B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : IsCompl (TauCeti.derivationCompLieHom (B := R) f).range.toSubmodule
      (TauCeti.derivationCompLieHom (B := R) g).range.toSubmodule) :
    Function.Bijective (affineMulTangent f g) := by
  apply (affineMulTangent_bijective_iff f g).mpr
  let eF := (TauCeti.derivationCompLieHom (B := R) f).equivRangeOfInjective
    (TauCeti.derivationCompLieHom_injective_of_surjective f hf)
  let eG := (TauCeti.derivationCompLieHom (B := R) g).equivRangeOfInjective
    (TauCeti.derivationCompLieHom_injective_of_surjective g hg)
  let eP := LinearEquiv.prodCongr eF.toLinearEquiv eG.toLinearEquiv
  let eSum := Submodule.prodEquivOfIsCompl
    (TauCeti.derivationCompLieHom (B := R) f).range.toSubmodule
    (TauCeti.derivationCompLieHom (B := R) g).range.toSubmodule h
  exact (eP.trans eSum).bijective

end

end GroupActions
