import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
import TauCeti.Algebra.AlgebraicGroup.Tangent.CounitPoints
import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# Adjoint Differential Naturality

Differentials of affine group morphisms commute with the adjoint action. -/

noncomputable section
namespace ReductiveGroups

open WithConv

variable {K A A' : Type*} [Field K]
  [CommRing A] [HopfAlgebra K A]
  [CommRing A'] [HopfAlgebra K A']

/-- The equality is

```lean
TauCeti.derivationComp (B := K) φ
      (Derivation.adDerivation K
        ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K A K).symm g) d) =
    Derivation.adDerivation K
      ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K A' K).symm
        (TauCeti.AlgHom.mapDomain φ g))
      (TauCeti.derivationComp (B := K) φ d)
```
-/
theorem derivationComp_adDerivation
    (φ : A' →ₐc[K] A) (g : WithConv (A →ₐ[K] K))
    (d : Derivation K A (TauCeti.Bialgebra.CounitAlgebra K A K)) :
    TauCeti.derivationComp (B := K) φ
      (Derivation.adDerivation K
        ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K A K).symm g) d) =
    Derivation.adDerivation K
      ((TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K A' K).symm
        (TauCeti.AlgHom.mapDomain φ g))
      (TauCeti.derivationComp (B := K) φ d) := by
  let ga := (TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K A K).symm g
  let gb := (TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K A' K).symm
    (TauCeti.AlgHom.mapDomain φ g)
  have hga (a : A) : ga.ofConv a = g.ofConv a := by
    simp [ga, TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply,
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_symm_apply]
    rfl
  have hgb (a : A') : gb.ofConv a = g.ofConv (φ a) := by
    simp [gb,
      TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply,
      TauCeti.Bialgebra.CounitAlgebra.algEquivSelf_symm_apply]
    rfl
  have hginv (a : A') : (gb⁻¹).ofConv a = (ga⁻¹).ofConv (φ a) := by
    have ha : ga⁻¹ =
        (TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K A K).symm (g⁻¹) := by
      exact (map_inv (TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K A K).symm g).symm
    have hb : gb⁻¹ =
        (TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K A' K).symm
          ((TauCeti.AlgHom.mapDomain φ g)⁻¹) := by
      exact (map_inv (TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv K A' K).symm
        (TauCeti.AlgHom.mapDomain φ g)).symm
    rw [ha, hb]
    simp only [TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply]
    change ((TauCeti.AlgHom.mapDomain φ g)⁻¹).ofConv a = (g⁻¹).ofConv (φ a)
    rw [← map_inv (TauCeti.AlgHom.mapDomain φ) g]
    rfl
  have hpre_g : ga.ofConv.toLinearMap.comp
      (φ : A' →ₐ[K] A).toLinearMap = gb.ofConv.toLinearMap := by
    ext a
    exact (hga (φ a)).trans (hgb a).symm
  have hpre_d : (d : A →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K A K).comp
      (φ : A' →ₐ[K] A).toLinearMap =
        (TauCeti.derivationComp (B := K) φ d :
          A' →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K A' K) := by
    ext a
    exact (TauCeti.derivationComp_apply φ d a).symm
  have hpre_inv : (ga⁻¹).ofConv.toLinearMap.comp
      (φ : A' →ₐ[K] A).toLinearMap = (gb⁻¹).ofConv.toLinearMap := by
    ext a
    exact (hginv a).symm
  have hφ : (φ : A' →ₐ[K] A).toLinearMap =
      (φ : A' →ₗc[K] A).toLinearMap := by
    rw [CoalgHom.toLinearMap_eq_ofClass]
    exact BialgHom.toAlgHom_toLinearMap φ
  have htri :
      (toConv ga.ofConv.toLinearMap *
          toConv (d : A →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K A K) *
          toConv (ga⁻¹).ofConv.toLinearMap).ofConv.comp
            (φ : A' →ₐ[K] A).toLinearMap =
        (toConv gb.ofConv.toLinearMap *
          toConv (TauCeti.derivationComp (B := K) φ d :
            A' →ₗ[K] TauCeti.Bialgebra.CounitAlgebra K A' K) *
          toConv (gb⁻¹).ofConv.toLinearMap).ofConv := by
    rw [hφ, LinearMap.convMul_comp_coalgHom_distrib]
    rw [LinearMap.convMul_comp_coalgHom_distrib]
    rw [← hφ, hpre_g, hpre_d, hpre_inv]
    simp only [toConv_ofConv]
    rfl
  apply Derivation.ext
  intro a
  rw [TauCeti.derivationComp_apply]
  rw [Derivation.adDerivation_apply, Derivation.adDerivation_apply]
  exact DFunLike.congr_fun htri a

end ReductiveGroups
