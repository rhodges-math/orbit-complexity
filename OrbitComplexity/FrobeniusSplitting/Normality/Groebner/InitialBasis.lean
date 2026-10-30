import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-! Finite monic leading families for polynomial ideals over a field. -/

open MvPolynomial

namespace FrobeniusSplitting

variable {σ K : Type*} [Finite σ] [Field K] (m : MonomialOrder σ)

omit [Finite σ] in
private theorem monic_normalize {f : MvPolynomial σ K} (hf : f ≠ 0) :
    m.Monic ((m.leadingCoeff f)⁻¹ • f) ∧
      m.degree ((m.leadingCoeff f)⁻¹ • f) = m.degree f := by
  have hc : m.leadingCoeff f ≠ 0 := m.leadingCoeff_ne_zero_iff.mpr hf
  have hd := m.degree_smul_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (inv_ne_zero hc)) (f := f)
  refine ⟨?_, hd⟩
  change ((m.leadingCoeff f)⁻¹ • f).coeff
    (m.degree ((m.leadingCoeff f)⁻¹ • f)) = 1
  rw [hd, coeff_smul]
  exact inv_mul_cancel₀ hc

/-- Every polynomial ideal over a field has a finite monic leading family. -/
theorem exists_initial_monic (I : Ideal (MvPolynomial σ K)) :
    ∃ t : Finset (MvPolynomial σ K),
      (∀ b ∈ t, b ∈ I ∧ m.Monic b) ∧
      ∀ f ∈ I, f ≠ 0 → ∃ b ∈ t, m.degree b ≤ m.degree f := by
  classical
  let B : Set (MvPolynomial σ K) := {f | f ∈ I ∧ m.Monic f}
  let D : Set (σ →₀ ℕ) := m.degree '' B
  let J : Ideal (MvPolynomial σ K) :=
    Ideal.span ((fun d => monomial d (1 : K)) '' D)
  obtain ⟨s, hs, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset
      ((fun d => monomial d (1 : K)) '' D)).mp (IsNoetherian.noetherian J)
  have hex : ∀ x : s, ∃ b : MvPolynomial σ K,
      b ∈ B ∧ monomial (m.degree b) (1 : K) = (x : MvPolynomial σ K) := by
    intro x
    obtain ⟨d, ⟨b, hb, rfl⟩, h⟩ := hs x.property
    exact ⟨b, hb, h⟩
  choose b hb he using hex
  let t : Finset (MvPolynomial σ K) := Finset.univ.image b
  have hst : (s : Set (MvPolynomial σ K)) =
      (fun d => monomial d (1 : K)) '' (m.degree '' (t : Set (MvPolynomial σ K))) := by
    ext x
    constructor
    · intro hx
      refine ⟨m.degree (b ⟨x, hx⟩), ?_, he ⟨x, hx⟩⟩
      exact ⟨b ⟨x, hx⟩, Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨d, ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
      change monomial (m.degree (b i)) (1 : K) ∈ (s : Set (MvPolynomial σ K))
      exact Eq.mpr (congrArg (fun p : MvPolynomial σ K => p ∈ s) (he i)) i.property
  refine ⟨t, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    exact hb i
  · intro f hf hn
    obtain ⟨hmonic, hdegree⟩ := monic_normalize m hn
    have hB : (m.leadingCoeff f)⁻¹ • f ∈ B :=
      ⟨by simpa [smul_eq_C_mul] using I.mul_mem_left (C (m.leadingCoeff f)⁻¹) hf,
        hmonic⟩
    have hm : monomial (m.degree f) (1 : K) ∈ J := by
      apply Ideal.subset_span
      exact ⟨m.degree f, ⟨_, hB, hdegree⟩, rfl⟩
    rw [show J = Ideal.span (s : Set (MvPolynomial σ K)) from hspan, hst] at hm
    obtain ⟨d, ⟨g, hg, rfl⟩, hd⟩ :=
      (mem_ideal_span_monomial_image.mp hm) (m.degree f) (by simp)
    exact ⟨g, hg, hd⟩

end FrobeniusSplitting
