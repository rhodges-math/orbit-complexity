import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! Freeness of polynomial quotients from monic leading families. -/

open MvPolynomial

namespace FrobeniusSplitting

variable {σ R ι : Type*} [CommRing R] (m : MonomialOrder σ)

/-- Standard polynomials identify with the quotient by a monic leading family. -/
noncomputable def standardMonomialEquiv (I : Ideal (MvPolynomial σ R))
    (b : ι → MvPolynomial σ R) (hb : ∀ i, b i ∈ I)
    (hmonic : ∀ i, m.Monic (b i))
    (hinitial : ∀ f ∈ I, f ≠ 0 → ∃ i, m.degree (b i) ≤ m.degree f) :
    AddMonoidAlgebra.supported R R {d | ∀ i, ¬ m.degree (b i) ≤ d} ≃ₗ[R]
      (MvPolynomial σ R ⧸ I) := by
  classical
  let D : Set (σ →₀ ℕ) := {d | ∀ i, ¬ m.degree (b i) ≤ d}
  let V := AddMonoidAlgebra.supported R R D
  let q : V →ₗ[R] (MvPolynomial σ R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).toLinearMap.comp V.subtype
  have hinj : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro r hr
    apply Subtype.ext
    change (r : MvPolynomial σ R) = 0
    by_contra hn
    have hmem : (r : MvPolynomial σ R) ∈ I :=
      Ideal.Quotient.eq_zero_iff_mem.mp hr
    obtain ⟨i, hi⟩ := hinitial r hmem hn
    exact (r.property ((m.degree_mem_support_iff _).mpr hn) i) hi
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨g, r, hf, _, hr⟩ :=
      m.div (fun i => (hmonic i) ▸ isUnit_one) f
    have hcomb : Finsupp.linearCombination (MvPolynomial σ R) b g ∈ I := by
      rw [Finsupp.linearCombination_apply]
      exact Submodule.sum_mem I fun i _ => I.smul_mem (g i) (hb i)
    refine ⟨⟨r, hr⟩, ?_⟩
    change Ideal.Quotient.mk I r = Ideal.Quotient.mk I f
    rw [hf, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hcomb, zero_add]
  exact LinearEquiv.ofBijective q ⟨hinj, hsurj⟩

/-- The standard-monomial equivalence sends a polynomial to its quotient class. -/
theorem standardMonomialEquiv_apply (I : Ideal (MvPolynomial σ R))
    (b : ι → MvPolynomial σ R) (hb : ∀ i, b i ∈ I)
    (hmonic : ∀ i, m.Monic (b i))
    (hinitial : ∀ f ∈ I, f ≠ 0 → ∃ i, m.degree (b i) ≤ m.degree f)
    (r : AddMonoidAlgebra.supported R R {d | ∀ i, ¬ m.degree (b i) ≤ d}) :
    standardMonomialEquiv m I b hb hmonic hinitial r =
      Ideal.Quotient.mk I (r : MvPolynomial σ R) := rfl

/-- A monic leading family gives a free module of standard monomials. -/
theorem free_quotient_of_initial_monic (I : Ideal (MvPolynomial σ R))
    (b : ι → MvPolynomial σ R) (hb : ∀ i, b i ∈ I)
    (hmonic : ∀ i, m.Monic (b i))
    (hinitial : ∀ f ∈ I, f ≠ 0 → ∃ i, m.degree (b i) ≤ m.degree f) :
    Module.Free R (MvPolynomial σ R ⧸ I) := by
  let D : Set (σ →₀ ℕ) := {d | ∀ i, ¬ m.degree (b i) ≤ d}
  let : Module.Free R (AddMonoidAlgebra.supported R R D) :=
    Module.Free.of_equiv (AddMonoidAlgebra.supportedEquivFinsupp (R := R) D).symm
  exact Module.Free.of_equiv (standardMonomialEquiv m I b hb hmonic hinitial)

end FrobeniusSplitting
