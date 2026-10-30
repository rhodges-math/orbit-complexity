import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.EliminationInclusion

/-! Polynomial quotient comparisons with their coefficient maps retained. -/

open MvPolynomial
open scoped TensorProduct

namespace FrobeniusSplitting

variable {σ R K : Type*} [CommRing R] [CommRing K] [Algebra R K]

/-- Scalar extension of a polynomial quotient identifies with the quotient by its extended ideal. -/
noncomputable def polynomialQuotientEquiv (I : Ideal (MvPolynomial σ R))
    (J : Ideal (MvPolynomial σ K)) (h : I.map (map (algebraMap R K)) = J) :
    K ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[K] (MvPolynomial σ K ⧸ J) := by
  let e : K ⊗[R] MvPolynomial σ R ≃ₐ[K] MvPolynomial σ K :=
    MvPolynomial.algebraTensorAlgEquiv R K
  let u : MvPolynomial σ R →+* K ⊗[R] MvPolynomial σ R :=
    (Algebra.TensorProduct.includeRight :
      MvPolynomial σ R →ₐ[R] K ⊗[R] MvPolynomial σ R).toRingHom
  have he : (e : _ →+* _).comp u = map (algebraMap R K) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[R] p) = map (algebraMap R K) p
    exact (MvPolynomial.algebraTensorAlgEquiv_tmul (R := R) (A := K) 1 p).trans
      (one_smul K _)
  have hJ : J = (I.map u).map (e : _ →+* _) := by
    rw [Ideal.map_map, he]
    exact h.symm
  exact (Algebra.TensorProduct.tensorQuotientEquiv K (MvPolynomial σ R) K I).trans
    (Ideal.quotientEquivAlg (I.map u) J e hJ)

/-- The polynomial quotient comparison sends a pure tensor along the coefficient map. -/
theorem polynomialQuotientEquiv_tmul (I : Ideal (MvPolynomial σ R))
    (J : Ideal (MvPolynomial σ K)) (h : I.map (map (algebraMap R K)) = J)
    (a : K) (p : MvPolynomial σ R) :
    polynomialQuotientEquiv I J h (a ⊗ₜ[R] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk J (a • map (algebraMap R K) p) := by
  dsimp only [polynomialQuotientEquiv]
  erw [AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, MvPolynomial.algebraTensorAlgEquiv_tmul]

/-- Polynomial quotient comparisons intertwine the original retained-variable map. -/
theorem polynomialQuotientEquiv_rename {τ : Type*}
    (J : Ideal (MvPolynomial (τ ⊕ₗ σ) R)) (L : Ideal (MvPolynomial (τ ⊕ₗ σ) K))
    (hJ : J.map (map (algebraMap R K)) = L)
    (hA : (J.comap (rename (Sum.inrₗ : σ → τ ⊕ₗ σ)).toRingHom).map
      (map (algebraMap R K)) = L.comap (rename Sum.inrₗ).toRingHom)
    (z : K ⊗[R] (MvPolynomial σ R ⧸ J.comap (rename Sum.inrₗ).toRingHom)) :
    polynomialQuotientEquiv J L hJ
      (Algebra.TensorProduct.lTensor (S := K) K (eliminationQuotientMap J) z) =
      eliminationQuotientMap L
        (polynomialQuotientEquiv _ _ hA z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, eliminationQuotientMap_mk, polynomialQuotientEquiv_tmul]
    apply congrArg (Ideal.Quotient.mk L)
    have hs : rename (Sum.inrₗ : σ → τ ⊕ₗ σ)
        (a • map (algebraMap R K) p) = a • rename Sum.inrₗ (map (algebraMap R K) p) :=
      (rename Sum.inrₗ : MvPolynomial σ K →ₐ[K]
        MvPolynomial (τ ⊕ₗ σ) K).toLinearMap.map_smul a _
    rw [hs, map_rename]
  | add x y hx hy => simp only [map_add, hx, hy]

end FrobeniusSplitting
