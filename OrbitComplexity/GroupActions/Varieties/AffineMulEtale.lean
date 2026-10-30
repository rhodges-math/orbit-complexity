import OrbitComplexity.GroupActions.Varieties.AffineMulTranslations
import OrbitComplexity.GroupActions.Varieties.AffineMulTangents
import OrbitComplexity.GroupActions.Varieties.RationalDifferentials
import Mathlib.RingTheory.RingHom.Etale

/-!
# Etaleness of restricted affine multiplication

A bijective identity differential of restricted multiplication becomes bijective at all
rational points by translations. The rational-point differential criterion then proves etaleness.

## Main results

* `GroupActions.affineMulMap_etale`: identity differential criterion for multiplication.
-/

open scoped TensorProduct

namespace GroupActions

noncomputable section

universe u

variable {K H A B : Type u} [Field K]
  [CommRing H] [HopfAlgebra K H]
  [CommRing A] [HopfAlgebra K A]
  [CommRing B] [HopfAlgebra K B]

private theorem affineMulTangent_bijective_point (f : H →ₐc[K] A) (g : H →ₐc[K] B) :
    Function.Bijective (affineMulTangent f g) ↔
      Function.Bijective (pointDerivationPrecomp (affineMulMap f.toAlgHom g.toAlgHom)
        (Bialgebra.counitAlgHom K (A ⊗[K] B))) := by
  let eIn := (counitPointDerivEquiv K (A ⊗[K] B)).symm
  let eOut := (pointDerivationCongr (counit_comp_affineMulMap f g)).trans
    (counitPointDerivEquiv K H)
  let F := pointDerivationPrecomp (affineMulMap f.toAlgHom g.toAlgHom)
    (Bialgebra.counitAlgHom K (A ⊗[K] B))
  change Function.Bijective (eOut ∘ F ∘ eIn) ↔ Function.Bijective F
  exact (EquivLike.bijective_comp eIn (eOut ∘ F)).trans (EquivLike.comp_bijective F eOut)

variable [IsAlgClosed K]
  [Algebra.FiniteType K H] [IsReduced H]
  [Algebra.FiniteType K A] [IsReduced A]
  [Algebra.FiniteType K B] [IsReduced (A ⊗[K] B)]
  [Algebra.Smooth K H] [Algebra.Smooth K (A ⊗[K] B)]

/-- Restricted multiplication is etale when its identity differential is bijective. -/
theorem affineMulMap_etale (f : H →ₐc[K] A) (g : H →ₐc[K] B)
    (h : Function.Bijective (affineMulTangent f g)) :
    (affineMulMap f.toAlgHom g.toAlgHom).toRingHom.Etale := by
  let μ := affineMulMap f.toAlgHom g.toAlgHom
  let : Algebra H (A ⊗[K] B) := μ.toRingHom.toAlgebra
  let : IsScalarTower K H (A ⊗[K] B) := IsScalarTower.of_algHom μ
  let : Algebra.FiniteType K (A ⊗[K] B) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K A)
      (inferInstance : Algebra.FiniteType A (A ⊗[K] B))
  let : Algebra.FiniteType H (A ⊗[K] B) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K H (A ⊗[K] B)
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing K H
  let : Algebra.FinitePresentation H (A ⊗[K] B) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  change Algebra.Etale H (A ⊗[K] B)
  apply etale_of_bijective_rationalDerivs K H (A ⊗[K] B)
  intro q
  have hμ : IsScalarTower.toAlgHom K H (A ⊗[K] B) = μ := by ext; rfl
  rw [hμ]
  exact affineMulMap_deriv_bijective f g ((affineMulTangent_bijective_point f g).mp h) q

end

end GroupActions
