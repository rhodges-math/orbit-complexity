import OrbitComplexity.FrobeniusSplitting.Normality.Groebner.StandardMonomials
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! Split inclusions from compatible standard monomials. -/

open MvPolynomial

namespace FrobeniusSplitting

variable {σ τ R ι κ : Type*} [CommRing R]

private noncomputable def supportedProjection (D : Set (σ →₀ ℕ)) :
    MvPolynomial σ R →ₗ[R] AddMonoidAlgebra.supported R R D := by
  classical
  exact (AddMonoidAlgebra.supportedEquivFinsupp (R := R) D).symm.toLinearMap.comp
    ((Finsupp.lsubtypeDomain D).comp
      (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap)

private theorem supportedProjection_subtype (D : Set (σ →₀ ℕ))
    (r : AddMonoidAlgebra.supported R R D) :
    supportedProjection D (r : MvPolynomial σ R) = r := by
  classical
  change (AddMonoidAlgebra.supportedEquivFinsupp (R := R) D).symm
    ((AddMonoidAlgebra.supportedEquivFinsupp (R := R) D) r) = r
  exact LinearEquiv.symm_apply_apply _ r

/-- Compatible standard monomials split an induced polynomial-quotient inclusion. -/
theorem split_quotient_rename (m : MonomialOrder σ) (n : MonomialOrder τ)
    (I : Ideal (MvPolynomial σ R)) (J : Ideal (MvPolynomial τ R))
    (a : ι → MvPolynomial σ R) (b : κ → MvPolynomial τ R)
    (ha : ∀ i, a i ∈ I) (hb : ∀ j, b j ∈ J)
    (ham : ∀ i, m.Monic (a i)) (hbm : ∀ j, n.Monic (b j))
    (hai : ∀ p ∈ I, p ≠ 0 → ∃ i, m.degree (a i) ≤ m.degree p)
    (hbi : ∀ p ∈ J, p ≠ 0 → ∃ j, n.degree (b j) ≤ n.degree p)
    (e : σ → τ) (he : Function.Injective e)
    (hs : ∀ d, (∀ i, ¬ m.degree (a i) ≤ d) →
      ∀ j, ¬ n.degree (b j) ≤ d.mapDomain e)
    (f : (MvPolynomial σ R ⧸ I) →ₐ[R] (MvPolynomial τ R ⧸ J))
    (hf : ∀ p, f (Ideal.Quotient.mk I p) = Ideal.Quotient.mk J (rename e p)) :
    ∃ r : (MvPolynomial τ R ⧸ J) →ₗ[R] (MvPolynomial σ R ⧸ I),
      r.comp f.toLinearMap = LinearMap.id := by
  classical
  let D : Set (σ →₀ ℕ) := {d | ∀ i, ¬ m.degree (a i) ≤ d}
  let E : Set (τ →₀ ℕ) := {d | ∀ j, ¬ n.degree (b j) ≤ d}
  let A := AddMonoidAlgebra.supported R R D
  let B := AddMonoidAlgebra.supported R R E
  let qA : A ≃ₗ[R] (MvPolynomial σ R ⧸ I) :=
    standardMonomialEquiv m I a ha ham hai
  let qB : B ≃ₗ[R] (MvPolynomial τ R ⧸ J) :=
    standardMonomialEquiv n J b hb hbm hbi
  let v : A →ₗ[R] B :=
    { toFun := fun r => ⟨rename e (r : MvPolynomial σ R), by
        intro d hd
        change d ∈ (rename e (r : MvPolynomial σ R)).support at hd
        rw [support_rename_of_injective he] at hd
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
        exact hs c (r.property hc)⟩
      map_add' := fun r s => Subtype.ext
        ((rename e : MvPolynomial σ R →ₐ[R] MvPolynomial τ R).map_add
          (r : MvPolynomial σ R) (s : MvPolynomial σ R))
      map_smul' := fun c r => Subtype.ext
        ((rename e : MvPolynomial σ R →ₐ[R] MvPolynomial τ R).toLinearMap.map_smul
          c (r : MvPolynomial σ R)) }
  have hmap (r : A) : f (qA r) = qB (v r) := by
    change f (standardMonomialEquiv m I a ha ham hai r) =
      standardMonomialEquiv n J b hb hbm hbi (v r)
    simp only [standardMonomialEquiv_apply]
    exact hf r
  let r : (MvPolynomial τ R ⧸ J) →ₗ[R] (MvPolynomial σ R ⧸ I) :=
    qA.toLinearMap.comp ((supportedProjection D).comp
      ((killCompl he).toLinearMap.comp (B.subtype.comp qB.symm.toLinearMap)))
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := qA.surjective y
  change r (f (qA x)) = qA x
  rw [hmap]
  change qA (supportedProjection D
    (killCompl he ((qB.symm (qB (v x)) : B) : MvPolynomial τ R))) = qA x
  rw [qB.symm_apply_apply]
  change qA (supportedProjection D (killCompl he (rename e (x : MvPolynomial σ R)))) = _
  rw [killCompl_rename_app, supportedProjection_subtype]

end FrobeniusSplitting
